module TyRE.Core

import public Data.List
import public Data.Either
import public Data.SortedSet
import public Data.List1
import Data.SnocList

infixr 6 <*>, <*, *>

public export
data CharCond =
      OneOf (SortedSet Char)
    | Range (Char, Char)
    | Pred (Char -> Bool)

public export
Eq CharCond where
  (==) (OneOf x) (OneOf y) = x == y
  (==) (OneOf x) _ = False
  (==) (Range x) (Range y) = x == y
  (==) (Range x) _ = False
  (==) (Pred _) _ = False

public export
satisfies : CharCond -> Char -> Bool
satisfies (OneOf xs) = \c => contains c xs
satisfies (Range (x, y)) = \c => x <= c && c <= y
satisfies (Pred f) = \c => f c

public export
data TyRE : Type -> Type where
  Empty     : TyRE ()
  MatchChar : CharCond -> TyRE Char
  Group     : TyRE a -> TyRE String
  (<*>)     : {0 a,b : Type} -> TyRE a -> TyRE b -> TyRE (a, b)
  Conv      : {0 a,b : Type} -> TyRE a -> (a -> b) -> TyRE b
  (<|>)     : {0 a,b : Type} -> TyRE a -> TyRE b -> TyRE (Either a b)
  Rep       : {0 a   : Type} -> TyRE a -> TyRE (SnocList a)

public export
Functor TyRE where
  map f tyre = Conv tyre f

public export
predicate : (Char -> Bool) -> TyRE Char
predicate f = MatchChar (Pred f)

public export
empty : TyRE ()
empty = Empty

public export
any : TyRE Char
any = predicate (\_ => True)

public export
group : TyRE a -> TyRE String
group tyre = Group tyre

public export
ignore : TyRE a -> TyRE ()
ignore tyre = (\_ => ()) `map` (group tyre)

public export
range : Char -> Char -> TyRE Char
range x y = MatchChar (Range (x,y))

public export
digit : TyRE Integer
digit = (\c => cast c - cast '0') `map` range '0' '9'

public export
digitChar : TyRE Char
digitChar = range '0' '9'

public export
oneOfCharsList : List Char -> TyRE Char
oneOfCharsList xs = MatchChar (OneOf (fromList xs))

public export
oneOfChars : String -> TyRE Char
oneOfChars xs = oneOfCharsList (unpack xs)

public export
match : Char -> TyRE ()
match c = ignore $ oneOfCharsList [c]

public export
rep0 : TyRE a -> TyRE (List a)
rep0 tyre = cast `map` Rep tyre

public export
rep1 : TyRE a -> TyRE (List a)
rep1 tyre = (\(e,l) => e::l) `map` (tyre <*> rep0 tyre)

public export
rep1l1 : TyRE a -> TyRE (List1 a)
rep1l1 tyre = (\(e,l) => e:::l) `map` (tyre <*> rep0 tyre)

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
oneOf : List1 (TyRE a) -> TyRE a
oneOf (head ::: []) = head
oneOf (head ::: (x :: xs)) = oneOf $ (head `or` x) ::: xs

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
isConsuming (r1 <*> r2) = isConsuming r1 || isConsuming r2
isConsuming (Conv r f) = isConsuming r
isConsuming (r1 <|> r2) = isConsuming r1 && isConsuming r2
isConsuming (Rep r1) = False
isConsuming Empty = False
isConsuming (MatchChar _) = True
isConsuming (Group r) = isConsuming r

public export
data IsConsuming : TyRE a -> Type where
  ItIsConsuming : {re : TyRE a} -> {auto 0 prf : isConsuming re = True}
                -> IsConsuming re

leftBranchTrue : (a = True) -> (a || b = True)
leftBranchTrue Refl = Refl

rightBranchTrue : {a : Bool} -> (b = True) -> (a || b = True)
rightBranchTrue {a = False} Refl = Refl
rightBranchTrue {a = True} Refl = Refl
