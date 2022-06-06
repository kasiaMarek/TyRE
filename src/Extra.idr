module Extra

import Extra.Pred

import Data.List
import Data.SnocList
import Data.List.Elem
import Data.List.Elem.Extra
import public Data.List.Equalities

%default total

public export
extractBasedOnFst : (xs: List (a, b)) -> (xInXs: x `Elem` map Builtin.fst xs) -> b
extractBasedOnFst [] xInXs = absurd xInXs
extractBasedOnFst ((x, y) :: xs) Here = y
extractBasedOnFst (x' :: xs) (There pos) = extractBasedOnFst xs pos

public export
replicate : Nat -> (elem : a) -> SnocList a
replicate 0 elem = [<]
replicate (S k) elem = (replicate k elem) :< elem

export
bindSpec : (f : a -> List b) -> (p : Pred b) -> (q : Pred a) ->
  (spec : (x : a) -> (y: b ** (y `Elem` f x, p y)) -> q x) ->
  (cs : List a) ->
  (prf : (y: b ** (y `Elem` (cs >>= f), p y))) ->
  (x: a ** (x `Elem` cs, q x,(y: b ** (y `Elem` (f x),  p y))))

bindSpec f p q spec [] prf = absurd $ fst $ snd prf
bindSpec f p q spec (x :: xs) (y ** (isElemF, satP)) =
  let hereOrThere = elemAppLorR (f x) (xs >>= f) (replace {p=(y `Elem`)} (bindConcatPrf _ _ _) isElemF)
  in case hereOrThere of
    (Left prf1) => (x ** (Here, spec x (y ** (prf1, satP)), (y ** (prf1, satP))))
    (Right prf1) =>
      let (x ** (isElem, satQ, yInf)) = bindSpec f p q spec xs (y ** (prf1, satP))
      in (x ** (There isElem, satQ, yInf))

export
mapSpec : (f : (a, b) -> c) -> (q : Pred (a,b)) -> (p : Pred c) -> (xs: List (a,b))
        -> ((x1 : a) -> (x2 : b) -> p(f(x1, x2)) -> q (x1, x2)) -> (y: c)
        -> (y `Elem` map f xs, p y)
        -> (x1: a ** (x2:b ** (prf: x1 `Elem` map Builtin.fst xs ** (extractBasedOnFst xs prf = x2, f(x1, x2) = y, q (x1, x2)))))

mapSpec f q p [] spec y (isElem, satP) = absurd isElem
mapSpec f q p ((x1,x2) :: xs) spec y (pos, satP) =
  case pos of
    Here => (x1 ** (x2 ** (Here ** (Refl, Refl, spec x1 x2 satP))))
    There pos =>
      let (x1' ** (x2' ** (pos' ** (ex', eq', satQ')))) =
            mapSpec f q p xs spec y (pos, satP)
      in (x1' ** (x2' ** (There pos' ** (ex', eq', satQ'))))

-- export
-- extractBasedOnFstMapEq : (xs: List a) -> (ys : Vect (length xs) b)
--                       -> (f: b -> c) -> (pos : m `Elem` xs)
--                       -> (extractBasedOnFst xs (map f ys) pos = f (extractBasedOnFst xs ys pos))
-- extractBasedOnFstMapEq (x :: xs) (y :: ys) f Here = Refl
-- extractBasedOnFstMapEq (x :: xs) (y :: ys) f (There pos) = extractBasedOnFstMapEq xs ys f pos
-- public export
-- hereOrThereExtractBasedOnFst  : (xs: List a) -> (xs': List a) -> (ys: Vect (length xs) b) -> (ys': Vect (length xs') b)
--                               -> (xInXs: x `Elem` (xs ++ xs'))
--                               -> Either (pos: x `Elem` xs ** extractBasedOnFst (xs ++ xs') (replace {p=(\l => Vect l b)} (sym $ lengthDistributesOverAppend xs xs') (ys ++ ys')) xInXs = extractBasedOnFst xs ys pos)
--                                         (pos: x `Elem` xs' ** extractBasedOnFst (xs ++ xs') (replace {p=(\l => Vect l b)} (sym $ lengthDistributesOverAppend xs xs') (ys ++ ys')) xInXs = extractBasedOnFst xs' ys' pos)
--
--export
-- hereOrThereExtractBasedOnFst [] (x :: xs) [] (y :: ys) Here = Right (Here ** Refl)
-- hereOrThereExtractBasedOnFst [] (x' :: xs) [] (y :: ys) (There pos) =
--   let rest = hereOrThereExtractBasedOnFst [] xs [] ys pos
--   in case rest of
--     (Left (pos ** prf)) => absurd pos
--     (Right (pos ** prf)) => Right (There pos ** prf)

-- hereOrThereExtractBasedOnFst (x :: xs) xs' (y :: ys) ys' Here = Left (Here ** Refl)
-- hereOrThereExtractBasedOnFst (x' :: xs) xs' (y :: ys) ys' (There pos) =
--   case hereOrThereExtractBasedOnFst xs xs' ys ys' pos of
--     (Left (pos ** prf)) => Left (There pos ** prf)
--     (Right (pos ** prf)) => Right (pos ** prf)

-- public export
-- mapExtractBasedOnFst  : (f: b -> c) -> (xs : List a) -> (ys: Vect (length xs) b)
--                       -> (pos : x `Elem` xs)
--                       -> (extractBasedOnFst xs (map f ys) pos
--                             = f (extractBasedOnFst xs ys pos))
-- mapExtractBasedOnFst f (_ :: xs) (y :: ys) Here = Refl
-- mapExtractBasedOnFst f (x' :: xs) (y :: ys) (There pos) = mapExtractBasedOnFst f xs ys pos

-- public export
-- rightCantBeElemOfLeft : (x : a) -> (xs : List b) -> (Not ((Right x) `Elem` (map (Left . f) xs)))
-- rightCantBeElemOfLeft _ [] Here impossible
-- rightCantBeElemOfLeft _ [] (There y) impossible
-- rightCantBeElemOfLeft x (z :: xs) (There y) = rightCantBeElemOfLeft x xs y

-- public export
-- extractBasedOnFstFromRep  : (xs: List a) -> (rep : b) -> (pos: e `Elem` xs)
--                           -> (extractBasedOnFst xs (replicate (length xs) rep) pos = rep)

-- extractBasedOnFstFromRep (_ :: xs) rep Here = Refl
-- extractBasedOnFstFromRep (y :: xs) rep (There x) = extractBasedOnFstFromRep xs rep x

-- public export
-- mapF : (f : (a,b) -> c) -> (xs : List a) -> (ys : Vect (length xs) b) -> List c
-- mapF f [] [] = []
-- mapF f (x :: xs) (y :: ys) = (f (x,y)) :: (mapF f xs ys)

-- ||| Proof that if an element is found on the list it belongs to that list.
-- public export
-- foundImpliesExists : (xs : List a) -> (pred : a -> Bool) -> (0 prf : find pred xs = Just e) -> (e : a ** (e `Elem` xs, pred e = True))
-- foundImpliesExists [] _ Refl impossible
-- foundImpliesExists (x :: xs) pred prf with (pred x) proof p
--   foundImpliesExists (x :: xs) pred prf | False =
--     let (e ** (inTail, eq)) = foundImpliesExists xs pred prf
--     in (e ** (There inTail, eq))
--   foundImpliesExists (x :: xs) pred prf | True = (x ** (Here, p))

-- ||| Map Just
-- public export
-- mapJust : (f : a -> b) -> (m : Maybe a) -> (prf : map f m = Just e) -> (e': a ** (f e' = e, m = Just e'))
-- mapJust _ Nothing Refl impossible
-- mapJust f (Just x) Refl = (x ** (Refl, Refl))