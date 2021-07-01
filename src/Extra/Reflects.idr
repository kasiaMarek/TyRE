module Extra.Reflects

import Pred
import Data.List.Elem

public export
data Reflects : (p : a -> Type) -> (Maybe a) -> Type where
  Indeed    : {0 p : a -> Type} -> (prf : p x) -> Reflects p (Just x)
  Otherwise : {0 p : a -> Type} -> (prf : (x : a) -> Not (p x)) -> Reflects p Nothing

public export
record RMaybe {a : Type} p where
  constructor Because
  Holds   : Maybe a
  0 Proof : Reflects p Holds

public export
map : {0 p,q : a -> Type} -> p <-> q -> RMaybe p -> RMaybe q
map iff (Nothing `Because` (Otherwise nprf)) = Nothing `Because` ( Otherwise (\x => \qx => nprf x (iff.If x qx)))
map iff ((Just x) `Because` (Indeed prf)) = (Just x) `Because` (Indeed (iff.onlyIf x prf))

public export
findR : {0 a : Type} -> (pred : a -> Bool) -> (xs : List a) ->
  RMaybe (\x => (x `Elem` xs, pred x = True))

findR pred [] = Nothing `Because` Otherwise \x => \case (_, _) impossible

findR pred (x :: xs) with (pred x) proof p
  findR pred (x :: xs) | True = (Just x) `Because` (Indeed (Here, p))
  findR pred (x :: xs) | False =
    let iff: (\y => (y `Elem` (xs), pred y = True)) <-> (\y => (y `Elem` x :: xs,  pred y = True))
        iff = (\y => (\case
                     (Here, i) => absurd (trans (sym p) i)
                     (There e, c) => (e,c)
                  ))
              `And`
              (\_ => (\(e,v) => (There e, v)))
    in map iff (findR pred xs)
