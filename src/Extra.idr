module Extra

import Data.List
import Data.List.Elem
import Data.Vect
import Data.Vect.Elem
import Data.Maybe
import Pred
import Data.List.Equalities

%default total

||| Proof that if an element is found on the list it belongs to that list.
public export
foundImpliesExists : (xs : List a) -> (pred : a -> Bool) -> (0 prf : find pred xs = Just e) -> (e : a ** (e `Elem` xs, pred e = True))
foundImpliesExists [] _ Refl impossible
foundImpliesExists (x :: xs) pred prf with (pred x) proof p
  foundImpliesExists (x :: xs) pred prf | False =
    let (e ** (inTail, eq)) = foundImpliesExists xs pred prf
    in (e ** (There inTail, eq))
  foundImpliesExists (x :: xs) pred prf | True = (x ** (Here, p))

||| Map Just
public export
mapJust : (f : a -> b) -> (m : Maybe a) -> (prf : map f m = Just e) -> (e': a ** (f e' = e, m = Just e'))
mapJust _ Nothing Refl impossible
mapJust f (Just x) Refl = (x ** (Refl, Refl))

||| Extract value from Just
public export
fromJust: (m: Maybe a) -> (prf: m = Just x) -> a
fromJust (Just x) Refl = x

||| Proof that if an element belongs to concatenetion of lists xs ++ ys it belongs either to xs of ys
public export
hereOrThereConcat: (xs: List a) -> (ys: List a) -> (e `Elem` (xs ++ ys)) -> Either (e `Elem` xs) (e `Elem` ys)
hereOrThereConcat [] ys pos = Right pos
hereOrThereConcat (e :: xs) ys Here = Left Here
hereOrThereConcat (x :: xs) ys (There pos) = case hereOrThereConcat xs ys pos of
                                              (Left pos) => Left $ There pos
                                              (Right pos) => Right pos

---bind proofs
foldLeftIsConcatPrfAux: (xs: List a) -> (ys: List b) -> (zs: List b) -> (f: a -> List b) -> (foldl (\acc, elem => acc ++ f elem) (ys ++ zs) xs = ys ++ foldl (\acc, elem => acc ++ f elem) (zs) xs)
foldLeftIsConcatPrfAux [] ys zs f = Refl
foldLeftIsConcatPrfAux (x :: xs) ys zs f =
  replace
    {p = \m => foldl (\acc, elem => acc ++ f elem) m xs = ys ++ foldl (\acc, elem => acc ++ f elem) (zs ++ f x) xs}
    (appendAssociative _ _ _)
    (foldLeftIsConcatPrfAux xs ys (zs ++ f x) f)

public export
foldLeftIsConcatPrf: (xs: List a) -> (x: a) -> (f: a -> List b) -> ((x::xs >>= f) = (f x) ++ (xs >>= f))
foldLeftIsConcatPrf xs x f =
  replace
    {p = \m => foldl (\acc, elem => acc ++ f elem) m xs = f x ++ foldl (\acc, elem => acc ++ f elem) [] xs}
    (appendNilRightNeutral _)
    (foldLeftIsConcatPrfAux xs (f x) [] f)

public export
bindSpec : (f : a -> List b) -> (p : Pred b) -> (q : Pred a) ->
  (spec : (x : a) -> (y: b ** (y `Elem` f x, p y)) -> q x) ->
  (cs : List a) ->
  (prf : (y: b ** (y `Elem` (cs >>= f), p y))) ->
  (x: a ** (x `Elem` cs, q x,(y: b ** (y `Elem` (f x),  p y))))

bindSpec f p q spec [] prf = absurd $ fst $ snd prf
bindSpec f p q spec (x :: xs) (y ** (isElemF, satP)) =
  let hereOrThere = hereOrThereConcat (f x) (xs >>= f) (replace {p=(y `Elem`)} (foldLeftIsConcatPrf _ _ _) isElemF)
  in case hereOrThere of
    (Left prf1) => (x ** (Here, spec x (y ** (prf1, satP)), (y ** (prf1, satP))))
    (Right prf1) =>
      let (x ** (isElem, satQ, yInf)) = bindSpec f p q spec xs (y ** (prf1, satP))
      in (x ** (There isElem, satQ, yInf))

public export
extractBasedOnFst : (xs: List a) -> (ys: Vect (length xs) b) -> (x : a) -> (xInXs: x `Elem` xs) -> b
extractBasedOnFst [] [] x xInXs = absurd xInXs
extractBasedOnFst (x :: xs) (z :: ys) x Here = z
extractBasedOnFst (x' :: xs) (z :: ys) x (There pos) = extractBasedOnFst xs ys x pos

public export
hereOrThereExtractBasedOnFst  : (xs: List a) -> (xs': List a) -> (ys: Vect (length xs) b) -> (ys': Vect (length xs') b)
                              -> (x : a) -> (xInXs: x `Elem` (xs ++ xs'))
                              -> Either (pos: x `Elem` xs ** extractBasedOnFst (xs ++ xs') (replace {p=(\l => Vect l b)} (sym $ lengthDistributesOverAppend xs xs') (ys ++ ys')) x xInXs = extractBasedOnFst xs ys x pos)
                                        (pos: x `Elem` xs' ** extractBasedOnFst (xs ++ xs') (replace {p=(\l => Vect l b)} (sym $ lengthDistributesOverAppend xs xs') (ys ++ ys')) x xInXs = extractBasedOnFst xs' ys' x pos)

hereOrThereExtractBasedOnFst [] (x :: xs) [] (y :: ys) x Here = Right (Here ** Refl)
hereOrThereExtractBasedOnFst [] (x' :: xs) [] (y :: ys) x (There pos) =
  let rest = hereOrThereExtractBasedOnFst [] xs [] ys x pos
  in case rest of
    (Left (pos ** prf)) => absurd pos
    (Right (pos ** prf)) => Right (There pos ** prf)

hereOrThereExtractBasedOnFst (x :: xs) xs' (y :: ys) ys' x Here = Left (Here ** Refl)
hereOrThereExtractBasedOnFst (x' :: xs) xs' (y :: ys) ys' x (There pos) =
  let rest = hereOrThereExtractBasedOnFst xs xs' ys ys' x pos
  in case rest of
    (Left (pos ** prf)) => Left (There pos ** prf)
    (Right (pos ** prf)) => Right (pos ** prf)

public export
mapExtractBasedOnFst: (f: b -> c) -> (xs : List a) -> (ys: Vect (length xs) b) -> (x : a) -> (pos : x `Elem` xs) -> (extractBasedOnFst xs (map f ys) x pos = f (extractBasedOnFst xs ys x pos))
mapExtractBasedOnFst f (_ :: xs) (y :: ys) x Here = Refl
mapExtractBasedOnFst f (x' :: xs) (y :: ys) x (There pos) = mapExtractBasedOnFst f xs ys x pos

public export
rightCantBeElemOfLeft : (x : a) -> (xs : List b) -> (Not ((Right x) `Elem` (map (Left . f) xs)))
rightCantBeElemOfLeft _ [] Here impossible
rightCantBeElemOfLeft _ [] (There y) impossible
rightCantBeElemOfLeft x (z :: xs) (There y) = rightCantBeElemOfLeft x xs y

public export
extractBasedOnFstFromRep  : (xs: List a) -> (rep : b) -> (pos: e `Elem` xs)
                          -> (extractBasedOnFst xs (replicate (length xs) rep) e pos = rep)

extractBasedOnFstFromRep (_ :: xs) rep Here = Refl
extractBasedOnFstFromRep (y :: xs) rep (There x) = extractBasedOnFstFromRep xs rep x
