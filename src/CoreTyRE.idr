module CoreTyRE

import public Core

infixr 6 <*>

public export
data CoreTyRE: Type -> Type where
  Untyped: (r : CoreRE) -> CoreTyRE (Shape r)
  (<*>) : CoreTyRE a -> CoreTyRE b -> CoreTyRE (a, b)
  Conv  : (a -> b) -> CoreTyRE a -> CoreTyRE b
  (<|>) : CoreTyRE a -> CoreTyRE b -> CoreTyRE (Either a b)
  --Rep: CoreTyRE a -> CoreTyRE (List a)

public export
compile : (CoreTyRE a) -> CoreRE
compile (Untyped r)   = r
compile (x <*> y)     = Concat (compile x) (compile y)
compile (Conv _ x)    = compile x
compile (x <|> y)     = Alt (compile x) (compile y)

public export
extract : (tyre: CoreTyRE a) -> (Shape $ compile tyre -> a)
extract (Untyped r) x             = x
extract (re1 <*> re2) (x, y)      = (extract re1 x, extract re2 y)
extract (Conv f re) y             = f $ extract re y
extract (re1 <|> re2)  (Left x)   = Left $ extract re1 x
extract (re1 <|> re2)  (Right x)  = Right $ extract re2 x
