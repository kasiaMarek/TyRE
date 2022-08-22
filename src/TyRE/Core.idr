module TyRE.Core

import Data.List
import Data.Either
import Data.SortedSet

import TyRE.CoreRE

infixr 6 <*>

public export
data TyRE : Type -> Type where
  Untyped : (r : CoreRE) -> TyRE (Shape r)
  (<*>)   : TyRE a -> TyRE b -> TyRE (a, b)
  Conv    : TyRE a -> (a -> b) -> TyRE b
  (<|>)   : TyRE a -> TyRE b -> TyRE (Either a b)
  Rep     : TyRE a -> TyRE (List a)

public export
Functor TyRE where
  map f tyre = Conv tyre f

export
compile : (TyRE a) -> CoreRE
compile (Untyped r)   = r
compile (x <*> y)     = Concat (compile x) (compile y)
compile (Conv x f)    = compile x
compile (x <|> y)     = Alt (compile x) (compile y)
compile (Rep re)      = Star (compile re)

export
extract : (tyre: TyRE a) -> (Shape (compile tyre) -> a)
extract (Untyped r) x             = x
extract (re1 <*> re2) (x, y)      = (extract re1 x, extract re2 y)
extract (Conv re f) y             = f $ extract re y
extract (re1 <|> re2)  (Left x)   = Left $ extract re1 x
extract (re1 <|> re2)  (Right x)  = Right $ extract re2 x
extract (Rep re) xs               = map (extract re) xs

export
predicate : (Char -> Bool) -> TyRE Char
predicate f = Untyped (CharPred (Pred f))

export
empty : TyRE ()
empty = Untyped Empty

export
any : TyRE Char
any = predicate (\_ => True)

export
group : TyRE a -> TyRE String
group tyre = Untyped (Group (compile tyre))

export
ignore : TyRE a -> TyRE ()
ignore tyre = (\_ => ()) `map` (group tyre)

export
range : Char -> Char -> TyRE Char
range x y = Untyped (CharPred (Range (x,y)))

export
digit : TyRE Integer
digit = (\c => cast c - cast '0') `map` range '0' '9'

export
digitChar : TyRE Char
digitChar = range '0' '9'

export
oneOfList : List Char -> TyRE Char
oneOfList xs = Untyped (CharPred (OneOf (fromList xs)))

export
oneOf : String -> TyRE Char
oneOf xs = oneOfList (unpack xs)

export
match : Char -> TyRE ()
match c = ignore $ oneOfList [c]

export
rep0 : TyRE a -> TyRE (List a)
rep0 tyre = Rep tyre

export
rep1 : TyRE a -> TyRE (List a)
rep1 tyre = (\(e,l) => e::l) `map` (tyre <*> Rep tyre)

export
option : TyRE a -> TyRE (Maybe a)
option tyre = (\e => case e of {(Left x) => Just x ; (Right _) => Nothing}) `map` tyre <|> empty

export
(*>) : TyRE a -> TyRE b -> TyRE b
(*>) t1 t2 = snd `map` (ignore t1 <*> t2)

export
(<*) : TyRE a -> TyRE b -> TyRE a
(<*) t1 t2 = fst `map` (t1 <*> ignore t2)

export
or : TyRE a -> TyRE a -> TyRE a
or t1 t2 = fromEither `map` (t1 <|> t2)

export
letter : TyRE Char
letter = range 'a' 'z' `or` range 'A' 'Z'

export
repFrom : Nat -> TyRE a -> TyRE (List a)
repFrom 0 re = rep0 re
repFrom (S k) re = (\(e,l) => e::l) `map` (re <*> repFrom k re)

export
repTo : Nat -> TyRE a -> TyRE (List a)
repTo 0 re = const [] `map` empty
repTo (S k) re = 
  optionalAdd `map` (option re <*> repTo k re) where
    optionalAdd : (Maybe a, List a) -> List a
    optionalAdd (Nothing, xs) = xs
    optionalAdd ((Just x), xs) = x::xs

export
repFromTo : (from : Nat) -> (to : Nat) -> {auto prf : from <= to = True} -> TyRE a -> TyRE (List a)
repFromTo 0 0 _ = const [] `map` empty
repFromTo 0 (S from) re = repTo (S from) re
repFromTo (S from) 0 re {prf} = absurd prf
repFromTo (S from) (S to) re = (\(e,l) => e::l) `map` (re <*> repFromTo from to re)

public export
repTimesType : (n : Nat) -> (reType : Type) -> Type
repTimesType 0 reType = Unit
repTimesType 1 reType = reType
repTimesType (S (S k)) reType = (reType, (repTimesType (S k) reType))

export
repTimes : (n : Nat)-> (re : TyRE a) -> TyRE (repTimesType n a)
repTimes 0 re = empty
repTimes 1 re = re
repTimes (S (S k)) re = re <*> repTimes (S k) re
