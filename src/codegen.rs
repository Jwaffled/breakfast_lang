use std::{collections::HashMap, fs::File, io::Write};

use cranelift::prelude::{isa::CallConv, settings::FlagsOrIsa, *};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataContext, Linkage, Module};

use crate::{
    ast::{BinaryOp, BinaryOpType, Expr, Literal, Stmt},
    lexer, parser,
};

pub fn generate_code(source: &str) -> Result<*const u8, String> {
    match lexer::lex_tokens(source.to_string()) {
        Ok(tokens) => match parser::parse(tokens) {
            Ok(ast) => {
                let mut jit = BreakfastJIT::new();
                match jit.compile(ast) {
                    Ok(ptr) => Ok(ptr),
                    Err(err) => Err(format!("Error generating code: {}", err)),
                }
            }
            Err(err) => Err(format!("ParserError: {:?}", err)),
        },
        Err(err) => Err(format!(
            "LexerError: {} on line {} col {}",
            err.message, err.line, err.col
        )),
    }
}

pub struct BreakfastJIT {
    module: JITModule,
    builder_ctx: FunctionBuilderContext,
    ctx: codegen::Context,
    data_ctx: DataContext,
}

impl BreakfastJIT {
    pub fn new() -> Self {
        let builder = JITBuilder::new(cranelift_module::default_libcall_names()).unwrap();
        let module = JITModule::new(builder);
        Self {
            builder_ctx: FunctionBuilderContext::new(),
            data_ctx: DataContext::new(),
            ctx: module.make_context(),
            module,
        }
    }

    pub fn compile(&mut self, stmts: Vec<Stmt>) -> Result<*const u8, String> {
        self.translate(stmts)?;

        // self.ctx
        //     .func
        //     .signature
        //     .returns
        //     .push(AbiParam::new(types::F64));

        let id = self
            .module
            .declare_function("main", Linkage::Export, &self.ctx.func.signature)
            .map_err(|err| err.to_string())?;

        let func = self
            .module
            .define_function(id, &mut self.ctx)
            .map_err(|err| err.to_string())?;

        self.module.clear_context(&mut self.ctx);

        self.module.finalize_definitions();

        let code = self.module.get_finalized_function(id);

        Ok(code)
    }

    pub fn translate(&mut self, stmts: Vec<Stmt>) -> Result<(), String> {
        let ptr = self.module.target_config().pointer_type();

        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_ctx);

        let entry_block = builder.create_block();

        builder.append_block_params_for_function_params(entry_block);

        builder.switch_to_block(entry_block);

        builder.seal_block(entry_block);

        let mut trans = Translator {
            ptr,
            builder,
            variables: HashMap::new(),
            module: &mut self.module,
            data_ctx: &mut self.data_ctx,
        };

        for stmt in stmts {
            trans.translate_stmt(stmt);
        }

        // trans.builder.ins().return_(&[]);

        trans.builder.finalize();

        match codegen::verify_function(&self.ctx.func, self.module.isa()) {
            Ok(()) => {}
            Err(err) => {
                panic!("Verifier errors: {}", err);
            }
        }

        println!("IR: \n{:?}", self.ctx.func);

        self.output_ir(&mut File::create("intermediate.clif").expect("Failed to create file"));

        Ok(())
    }

    fn output_ir(&self, file: &mut File) {
        file.write(format!("{:?}", self.ctx.func).as_bytes())
            .expect("Error when writing IR to file.");
    }
}

struct Translator<'a> {
    ptr: types::Type,
    builder: FunctionBuilder<'a>,
    variables: HashMap<String, Variable>,
    module: &'a mut JITModule,
    data_ctx: &'a mut DataContext,
}

impl<'a> Translator<'a> {
    fn translate_stmt(&mut self, stmt: Stmt) {
        match stmt {
            Stmt::Expr(expr) => {
                self.translate_expr(expr);
            }
            Stmt::Return(_, expr) => match expr {
                Some(expr) => {
                    let val = self.translate_expr(expr);
                    self.builder.ins().return_(&[val]);
                }
                None => {
                    self.builder.ins().return_(&[]);
                }
            },
            Stmt::Block(stmts) => {}
            _ => todo!(),
        }
    }

    fn translate_expr(&mut self, expr: Expr) -> Value {
        match expr {
            Expr::Binary(lhs, op, rhs) => self.translate_binary(lhs, op, rhs),
            Expr::Literal(literal) => self.translate_literal(literal),

            _ => unimplemented!("Stop using unimplemented instructions {:?}", expr),
        }
    }

    fn translate_binary(&mut self, lhs: Box<Expr>, op: BinaryOp, rhs: Box<Expr>) -> Value {
        let lhs = self.translate_expr(*lhs);
        let rhs = self.translate_expr(*rhs);
        match op.op_type {
            BinaryOpType::Plus => self.builder.ins().fadd(lhs, rhs),
            BinaryOpType::Minus => self.builder.ins().fsub(lhs, rhs),
            BinaryOpType::Star => self.builder.ins().fmul(lhs, rhs),
            BinaryOpType::Slash => self.builder.ins().fdiv(lhs, rhs),
            BinaryOpType::EqualEqualTaste => self.builder.ins().fcmp(FloatCC::Equal, lhs, rhs),
            BinaryOpType::GreaterThanTastier => {
                self.builder.ins().fcmp(FloatCC::GreaterThan, lhs, rhs)
            }
            BinaryOpType::LessThanTasteless => self.builder.ins().fcmp(FloatCC::LessThan, lhs, rhs),
        }
    }

    fn translate_literal(&mut self, literal: Literal) -> Value {
        match literal {
            Literal::False => self.builder.ins().bconst(self.ptr, false),
            Literal::True => self.builder.ins().bconst(self.ptr, true),
            Literal::Number(num) => self.builder.ins().f64const(num),
            Literal::String(str) => self.translate_string(str),
            Literal::Null => self.builder.ins().null(self.ptr),
        }
    }

    fn translate_string(&mut self, string: String) -> Value {
        let mut str = string.clone();
        str.push('\0');
        self.data_ctx.define(str.into_bytes().into_boxed_slice());
        let id = self
            .module
            .declare_anonymous_data(true, false)
            .map_err(|err| err.to_string())
            .unwrap();

        self.module
            .define_data(id, &self.data_ctx)
            .map_err(|err| err.to_string())
            .unwrap();
        self.data_ctx.clear();
        self.module.finalize_definitions();
        let local_id = self.module.declare_data_in_func(id, &mut self.builder.func);
        self.builder.ins().symbol_value(self.ptr, local_id)
    }
}

#[cfg(test)]
mod tests {
    use super::generate_code;

    #[test]
    fn test() -> Result<(), String> {
        let code = generate_code("plate 5#")?;
        let func = unsafe { std::mem::transmute::<_, fn() -> f64>(code) };
        println!("{}", func());
        Ok(())
    }
}
