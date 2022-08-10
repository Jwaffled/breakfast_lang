pub type TypeId = usize;

#[derive(Debug)]
pub enum Type {
    Number,
    Bool,
    List(Box<Type>),
    Func(
        /* arg types */ Vec<Type>,
        /* return type */ Box<Type>,
    ),
}

pub enum TypeInfo {
    Unknown,
    Ref(TypeId),
    Number,
    Bool,
    String,
    List(TypeId),
    Func(Vec<TypeId>, TypeId),
}
