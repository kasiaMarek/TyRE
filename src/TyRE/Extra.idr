module TyRE.Extra

import Data.List
import Data.SnocList
import Data.List.Elem
import Data.List.Elem.Extra
import public Data.List.Equalities

import TyRE.Extra.Pred

%default total

public export
extractBasedOnFst : (xs: List (a, b)) -> (xInXs: x `Elem` map Builtin.fst xs) -> b
extractBasedOnFst [] xInXs = absurd xInXs
extractBasedOnFst (x :: xs) Here = snd x
extractBasedOnFst (x' :: xs) (There pos) = extractBasedOnFst xs pos

export
extractBasedOnFstSpec : (xs : List a) 
                      -> (f : a -> (b, c)) -> (x : b) 
                      -> (xInXs : x `Elem` map Builtin.fst (map f xs)) 
                      -> (e : a ** extractBasedOnFst (map f xs) xInXs = Builtin.snd (f e))
extractBasedOnFstSpec [] _ _ Here impossible
extractBasedOnFstSpec [] _ _ (There y) impossible
extractBasedOnFstSpec (y :: xs) f (fst (f y)) Here = (y ** Refl)
extractBasedOnFstSpec (y :: xs) f x (There pos) = extractBasedOnFstSpec xs f x pos

export
extractBasedOnFstAppLor :  (xs : List (a, b)) 
                        -> (ys : List (a, b))
                        -> (x : a)
                        -> (xInApp  : x `Elem` map Builtin.fst (xs ++ ys)) 
                        -> Either (xInXs : x `Elem` map Builtin.fst xs
                                      ** extractBasedOnFst (xs ++ ys) xInApp = extractBasedOnFst xs xInXs)
                                  (xInYs : x `Elem` map Builtin.fst ys
                                      ** extractBasedOnFst (xs ++ ys) xInApp = extractBasedOnFst ys xInYs)
extractBasedOnFstAppLor [] ys x xInApp = Right (xInApp ** Refl)
extractBasedOnFstAppLor ((x, r) :: xs) ys x Here = Left (Here ** Refl)
extractBasedOnFstAppLor ((x', r') :: xs) ys x (There pos) = 
  case (extractBasedOnFstAppLor xs ys x pos) of
    Right (xInXs ** extractEq) => Right (xInXs ** extractEq)
    Left  (xInYs ** extractEq) => Left  (There xInYs ** extractEq)


public export
replicate : Nat -> (elem : a) -> SnocList a
replicate 0 elem = [<]
replicate (S k) elem = (replicate k elem) :< elem

export
replicateForSucc  : (k : Nat) -> (elem : a) 
                  -> ([< elem] ++ replicate k elem = replicate (S k) elem)
replicateForSucc 0 elem = Refl
replicateForSucc (S k) elem = cong (:< elem) (replicateForSucc k elem)

export
bindSpec : (f : a -> List b) -> (p : Pred b) -> (q : Pred a) ->
  (spec : (x : a) -> (y: b ** (y `Elem` f x, p y)) -> q x) ->
  (cs : List a) ->
  (prf : (y: b ** (y `Elem` (cs >>= f), p y))) ->
  (x : a ** (x `Elem` cs, q x,(y: b ** (y `Elem` (f x),  p y))))

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

export
biMapOnFst : (xs : List (a, c)) -> (f : a -> b) -> (g : c -> d) -> (map Builtin.fst (map (bimap f g) xs) = map f (map Builtin.fst xs))
biMapOnFst [] f g = Refl
biMapOnFst ((fst, snd) :: xs) f g = cong (f fst ::) (biMapOnFst xs f g)

export
elemMapRev : (xs : List a) -> (f : a -> b) -> {0 e : b} -> (e `Elem` map f xs) ->  (e' : a ** (e' `Elem` xs, f e' = e))
elemMapRev [] _ Here impossible
elemMapRev [] _ (There pos) impossible
elemMapRev (x :: xs) f Here = (x ** (Here, Refl))
elemMapRev (x :: xs) f (There pos) = 
    let (e' ** (pos', eq)) = elemMapRev xs f pos
    in (e' ** (There pos', eq))

export
eqForJust : (Just x = Just y) -> (x = y)
eqForJust Refl = Refl