module CoreTyRE

import public Core

infixr 6 <*>

public export
data CoreTyRE: Type -> Type where
  Untyped: (r : CoreRE) -> CoreTyRE (Shape r)
  (<*>) : CoreTyRE a -> CoreTyRE b -> CoreTyRE (a, b)
  Conv : (a -> b) -> CoreTyRE a -> CoreTyRE b
  --<|>: CoreTyRE a -> CoreTyRE b -> CoreTyRE (Either a b)
  --Rep: CoreTyRE a -> CoreTyRE (List a)

public export
compile : (CoreTyRE a) -> CoreRE
compile (Untyped r)   = r
compile (x <*> y)     = Concat (compile x) (compile y)
compile (Conv _ x)    = compile x

public export
extract : (tyre: CoreTyRE a) -> (Shape $ compile tyre -> a)
extract (Untyped r) x         = x
extract (y <*> z) (re1, re2)  = (extract y re1, extract z re2)
extract (Conv f y) re         = f $ extract y re
