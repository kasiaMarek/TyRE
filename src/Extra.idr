module Extra

import Data.List
import Data.List.Elem
import Data.Maybe

public export
foundImpliesExists : (xs : List a) -> (pred : a -> Bool) -> (prf : find pred xs = Just elem) -> (elem : a ** (elem `Elem` xs, pred elem = True))
foundImpliesExists [] _ Refl impossible
foundImpliesExists (x :: xs) pred prf with (pred x) proof p
  foundImpliesExists (x :: xs) pred prf | False =
    let (elem ** (inTail, eq)) = foundImpliesExists xs pred prf
    in (elem ** (There inTail, eq))
  foundImpliesExists (x :: xs) pred prf | True = (x ** (Here, p))

public export
mapMaybe : (f : a -> b) -> (m : Maybe a) -> (prf : map f m = Just e) -> (elem: a ** (f elem = e, m = Just elem))
mapMaybe _ Nothing Refl impossible
mapMaybe f (Just x) Refl = (x ** (Refl, Refl))
