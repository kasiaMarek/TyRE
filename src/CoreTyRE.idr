module CoreTyRE

import Core
import Codes

infixr 6 <*>

data CoreTyRE: Type -> Type where
  Untyped: (r : CoreRE) -> CoreTyRE (Shape r)
  (<*>): CoreTyRE a -> CoreTyRE b -> CoreTyRE (a, b)
  Conv: (a -> b) -> CoreTyRE a -> CoreTyRE b
  --<|>: CoreTyRE a -> CoreTyRE b -> CoreTyRE (Either a b)
  --Rep: CoreTyRE a -> CoreTyRE (List a)

compile : (CoreTyRE a) -> CoreRE
compile (Untyped r)   = r
compile (x <*> y)     = Concat (compile x) (compile y)
compile (Conv _ x)    = compile x

extract : (tyre: CoreTyRE a) -> (Shape $ compile tyre -> a)
extract (Untyped r) x         = x
extract (y <*> z) (re1, re2)  = (extract y re1, extract z re2)
extract (Conv f y) re         = f $ extract y re
