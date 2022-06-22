module Extra.Pred

public export
Pred : Type -> Type
Pred a = (x : a) -> Type

infix 3 <->
||| If and only if relation between predicates
public export
record (<->) {a : Type} (p, q : a -> Type) where
  constructor And
  If     : (x : a) -> (q x -> p x)
  onlyIf : (x : a) -> (p x -> q x)

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
