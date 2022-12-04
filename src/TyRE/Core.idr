module TyRE.Core

import public Data.List
import public Data.Either
import public Data.SortedSet
import Data.SnocList

import TyRE.CoreRE

infixr 6 <*>

public export
data TyRE : Type -> Type where
  Untyped : (r : CoreRE) -> TyRE (Shape r)
  (<*>)   : TyRE a -> TyRE b -> TyRE (a, b)
  Conv    : TyRE a -> (a -> b) -> TyRE b
  (<|>)   : TyRE a -> TyRE b -> TyRE (Either a b)
  Rep     : TyRE a -> TyRE (SnocList a)

public export
Functor TyRE where
  map f tyre = Conv tyre f

public export
compile : (TyRE a) -> CoreRE
compile (Untyped r)   = r
compile (x <*> y)     = Concat (compile x) (compile y)
compile (Conv x f)    = compile x
compile (x <|> y)     = Alt (compile x) (compile y)
compile (Rep re)      = Star (compile re)

public export
extract : (tyre : TyRE a) -> (Shape (compile tyre) -> a)
extract (Untyped r) x             = x
extract (re1 <*> re2) (x, y)      = (extract re1 x, extract re2 y)
extract (Conv re f) y             = f $ extract re y
extract (re1 <|> re2)  (Left x)   = Left $ extract re1 x
extract (re1 <|> re2)  (Right x)  = Right $ extract re2 x
extract (Rep re) xs               = map (extract re) xs

public export
predicate : (Char -> Bool) -> TyRE Char
predicate f = Untyped (CharPred (Pred f))

public export
empty : TyRE ()
empty = Untyped Empty

public export
any : TyRE Char
any = predicate (\_ => True)

public export
group : TyRE a -> TyRE String
group tyre = Untyped (Group (compile tyre))

public export
ignore : TyRE a -> TyRE ()
ignore tyre = (\_ => ()) `map` (group tyre)

public export
range : Char -> Char -> TyRE Char
range x y = Untyped (CharPred (Range (x,y)))

public export
digit : TyRE Integer
digit = (\c => cast c - cast '0') `map` range '0' '9'

public export
digitChar : TyRE Char
digitChar = range '0' '9'

public export
oneOfList : List Char -> TyRE Char
oneOfList xs = Untyped (CharPred (OneOf (fromList xs)))

public export
oneOf : String -> TyRE Char
oneOf xs = oneOfList (unpack xs)

public export
match : Char -> TyRE ()
match c = ignore $ oneOfList [c]

public export
rep0 : TyRE a -> TyRE (List a)
rep0 tyre = cast `map` Rep tyre

public export
rep1 : TyRE a -> TyRE (List a)
rep1 tyre = (\(e,l) => e::l) `map` (tyre <*> rep0 tyre)

public export
option : TyRE a -> TyRE (Maybe a)
option tyre = (\e => case e of {(Left x) => Just x ; (Right _) => Nothing}) `map` tyre <|> empty

public export
(*>) : TyRE a -> TyRE b -> TyRE b
(*>) t1 t2 = snd `map` (ignore t1 <*> t2)

public export
(<*) : TyRE a -> TyRE b -> TyRE a
(<*) t1 t2 = fst `map` (t1 <*> ignore t2)

public export
or : TyRE a -> TyRE a -> TyRE a
or t1 t2 = fromEither `map` (t1 <|> t2)

public export
letter : TyRE Char
letter = range 'a' 'z' `or` range 'A' 'Z'

public export
repFrom : Nat -> TyRE a -> TyRE (List a)
repFrom 0 re = rep0 re
repFrom (S k) re = (\(e,l) => e::l) `map` (re <*> repFrom k re)

public export
repTo : Nat -> TyRE a -> TyRE (List a)
repTo 0 re = const [] `map` empty
repTo (S k) re = 
  optionalAdd `map` (option re <*> repTo k re) where
    optionalAdd : (Maybe a, List a) -> List a
    optionalAdd (Nothing, xs) = xs
    optionalAdd ((Just x), xs) = x::xs

public export
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

public export
repTimes : (n : Nat)-> (re : TyRE a) -> TyRE (repTimesType n a)
repTimes 0 re = empty
repTimes 1 re = re
repTimes (S (S k)) re = re <*> repTimes (S k) re

public export
isConsuming : (re : TyRE a) -> Bool
isConsuming (Untyped r) = isConsuming r
isConsuming (r1 <*> r2) = isConsuming r1 || isConsuming r2
isConsuming (Conv r f) = isConsuming r
isConsuming (r1 <|> r2) = isConsuming r1 && isConsuming r2
isConsuming (Rep r1) = False

public export
data IsConsuming : TyRE a -> Type where
  ItIsConsuming : {re : TyRE a} -> {auto 0 prf : isConsuming re = True}
                -> IsConsuming re

leftBranchTrue : (a = True) -> (a || b = True)
leftBranchTrue Refl = Refl

rightBranchTrue : {a : Bool} -> (b = True) -> (a || b = True)
rightBranchTrue {a = False} Refl = Refl
rightBranchTrue {a = True} Refl = Refl

consumingImplAux : (tyre : TyRE a) -> (isConsuming tyre = True)
                -> (isConsuming (compile tyre) = True)
consumingImplAux (Untyped r) prf = prf
consumingImplAux (r1 <*> r2) prf with (isConsuming r1) proof p
  consumingImplAux (r1 <*> r2) prf | False
    = rightBranchTrue (consumingImplAux r2 prf)
  consumingImplAux (r1 <*> r2) prf | True
    = leftBranchTrue (consumingImplAux r1 p)
consumingImplAux (Conv r _) prf = consumingImplAux r prf
consumingImplAux (r1 <|> r2) prf with (isConsuming r1) proof p1 
                                    | (isConsuming r2) proof p2
  consumingImplAux (r1 <|> r2) prf | True | False impossible
  consumingImplAux (r1 <|> r2) prf | True | True
    = rewrite consumingImplAux r1 p1 in rewrite consumingImplAux r2 p2 in Refl
consumingImplAux (Rep r) prf impossible

export
consumingImpl : IsConsuming tyre -> IsConsuming (compile tyre)
consumingImpl (ItIsConsuming {re} {prf})
  = ItIsConsuming {prf = consumingImplAux re prf}
