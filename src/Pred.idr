module Pred

public export
Pred : Type -> Type
Pred a = (x : a) -> Type

infixr 4 /\
public export
(/\): {a: Type} -> (p : Pred a) -> (q : Pred a) -> Pred a
(/\) {a} p q x = (p x, q x)

infixr 4 \/
public export
(\/): {a: Type} -> (p : Pred a) -> (q : Pred a) -> Pred a
(\/) p q x = Either (p x) (q x)

public export
true: {a: Type} -> Pred a
true _ = Unit

public export
false: {a: Type} -> Pred a
false _ = Void
