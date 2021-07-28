module TyRE

import public Core
import Data.List

infixr 6 <*>

public export
data TyRE : Type -> Type where
  Untyped : (r : CoreRE) -> TyRE (Shape r)
  (<*>)   : TyRE a -> TyRE b -> TyRE (a, b)
  Conv    : (a -> b) -> TyRE a -> TyRE b
  (<|>)   : TyRE a -> TyRE b -> TyRE (Either a b)
  Rep     : TyRE a -> TyRE (List a)

export
compile : (TyRE a) -> CoreRE
compile (Untyped r)   = r
compile (x <*> y)     = Concat (compile x) (compile y)
compile (Conv _ x)    = compile x
compile (x <|> y)     = Alt (compile x) (compile y)
compile (Rep re)      = Star (compile re)

export
extract : (tyre: TyRE a) -> (Shape $ compile tyre -> a)
extract (Untyped r) x             = x
extract (re1 <*> re2) (x, y)      = (extract re1 x, extract re2 y)
extract (Conv f re) y             = f $ extract re y
extract (re1 <|> re2)  (Left x)   = Left $ extract re1 x
extract (re1 <|> re2)  (Right x)  = Right $ extract re2 x
extract (Rep re) xs               = map (extract re) xs

export
predicate : (Char -> Bool) -> TyRE Char
predicate f = Untyped (Pred f)

export
empty : TyRE ()
empty = Untyped Empty

export
any : TyRE Char
any = predicate (\_ => True)

export
ignore : TyRE a -> TyRE ()
ignore tyre = (\_ => ()) `Conv` tyre

export
match : Char -> TyRE ()
match c = ignore $ predicate (\e => e == c)

export
range : Char -> Char -> TyRE Char
range x y = predicate (\c =>  x <= c && c <= y)

export
digit : TyRE Integer
digit = (\c => cast c - cast '0') `Conv` range '0' '9'

export
oneOf : List Char -> TyRE Char
oneOf xs = predicate (\e => case (find (\x => e == x) xs) of {(Just _) => True ; Nothing => False})

export
rep0 : TyRE a -> TyRE (List a)
rep0 tyre = Rep tyre

export
rep1 : TyRE a -> TyRE (List a)
rep1 tyre = (\(e,l) => e::l) `Conv` (tyre <*> Rep tyre)

export
option : TyRE a -> TyRE (Maybe a)
option tyre = (\e => case e of {(Left x) => Just x ; (Right _) => Nothing}) `Conv` tyre <|> empty

export
(*>) : TyRE a -> TyRE b -> TyRE b
(*>) t1 t2 = snd `Conv` (t1 <*> t2)

export
(<*) : TyRE a -> TyRE b -> TyRE a
(<*) t1 t2 = fst `Conv` (t1 <*> t2)
