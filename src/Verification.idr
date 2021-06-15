module Verification

import NFA
import Evidence
import Data.List.Elem
import Data.List
import Extra
import Syntax.PreorderReasoning
import Data.List.Quantifiers

fromJust: (m: Maybe a) -> (prf: m = Just x) -> a
fromJust (Just x) Refl = x

foldLeftPrfAux: (xs: List a) -> (ys: List b) -> (zs: List b) -> (f: a -> List b) -> (foldl (\acc, elem => acc ++ f elem) (ys ++ zs) xs = ys ++ foldl (\acc, elem => acc ++ f elem) (zs) xs)
foldLeftPrfAux [] ys zs f = Refl
foldLeftPrfAux (x :: xs) ys zs f =
  replace
    {p = \m => foldl (\acc, elem => acc ++ f elem) m xs = ys ++ foldl (\acc, elem => acc ++ f elem) (zs ++ f x) xs}
    (appendAssociative _ _ _)
    (foldLeftPrfAux xs ys (zs ++ f x) f)

foldLeftPrf: (xs: List a) -> (x: a) -> (f: a -> List b) -> ((x::xs >>= f) = (f x) ++ (xs >>= f))
foldLeftPrf xs x f =
  replace
    {p = \m => foldl (\acc, elem => acc ++ f elem) m xs = f x ++ foldl (\acc, elem => acc ++ f elem) [] xs}
    (appendNilRightNeutral _)
    (foldLeftPrfAux xs (f x) [] f)

hereOrThereConcat: (xs: List a) -> (ys: List a) -> (elem `Elem` (xs ++ ys)) -> Either (elem `Elem` xs) (elem `Elem` ys)
hereOrThereConcat [] ys x = Right x
hereOrThereConcat (elem :: xs) ys Here = Left Here
hereOrThereConcat (y :: xs) ys (There x) =
  let tail = hereOrThereConcat xs ys x
  in case tail of
    (Left e) => Left $ There e
    (Right e) => Right e

Pred : Type -> Type
Pred a = (x : a) -> Type

bindSpec : (f : a -> List b) -> (p : Pred b) -> (q : Pred a) ->
  (spec : (x : a) -> (y: b ** (y `Elem` f x, p y)) -> q x) ->
  (cs : List a) ->
  (prf : (y: b ** (y `Elem` (cs >>= f), p y))) ->
  (x: a ** (x `Elem` cs, q x,(y: b ** (y `Elem` (f x),  p y))))

bindSpec f p q spec [] prf = absurd $ fst $ snd prf
bindSpec f p q spec (x :: xs) (y ** (isElemF, satP)) =
  let hereOrThere = hereOrThereConcat (f x) (xs >>= f) (replace {p=(y `Elem`)} (foldLeftPrf _ _ _) isElemF)
  in case hereOrThere of
    (Left prf1) => (x ** (Here, spec x (y ** (prf1, satP)), (y ** (prf1, satP))))
    (Right prf1) =>
      let (x ** (isElem, satQ, yInf)) = bindSpec f p q spec xs (y ** (prf1, satP))
      in (x ** (There isElem, satQ, yInf))

data AcceptingFrom : (nfa : NA) -> (s : nfa.State) -> (word : Word) -> Type where
  Accept : {auto nfa : NA} -> (s : nfa.State) -> (prf : nfa.accepting s = True) -> AcceptingFrom nfa s []
  Step   : {auto nfa : NA} -> (s : nfa.State) -> (c : Char) -> (t : nfa.State)
        -> (prf : t `Elem` (nfa.next s c))
        -> AcceptingFrom nfa t w
        -> AcceptingFrom nfa s (c :: w)

data Accepting : (nfa : NA) -> (word : Word) -> Type where
  Start : {auto nfa : NA} -> (s : nfa.State) -> (prf : s `Elem` nfa.start) -> AcceptingFrom nfa s w
       -> Accepting nfa w

runMappingSpec : {auto nfa : NA} -> {prog: Program nfa} -> (c: Char) -> (td : Thread nfa)
              -> (td': Thread nfa ** (td' `Elem` (runMapping prog c . step c) td, AcceptingFrom nfa (fst td') cs))
              -> AcceptingFrom nfa td.naState (c::cs)

runMappingSpec c td (td' ** (isElemOfF, accepts)) =
  let acc : AcceptingFrom nfa ((step c td) .naState) (c :: cs)
      acc = Step (fst (step c td)) c (td'.naState) (runFromStepState prog c (step c td) td' isElemOfF) accepts
  in replace {p=(\st => AcceptingFrom nfa st (c :: cs))} (fst $ (stepMaintainsState c td)) acc

recordPath : (nfa : NA) -> (prog : Program nfa) -> (tds : List (Thread nfa)) -> (str : Word)
          -> (prf : runFrom prog str tds = Just ev)
          -> (td : Thread nfa ** (td `Elem` tds, AcceptingFrom nfa (fst td) str))

recordPath nfa prog tds [] prf =
  let (x ** (_, woMap)) = mapMaybe _ _ prf
      (td ** (tdInTds, accept)) = foundImpliesExists _ _ woMap
  in (td ** (tdInTds, Accept (fst td) accept))

recordPath nfa prog tds (c :: cs) prf =
  let (x ** (isElem, satQ , _)) =
        bindSpec
          (runMapping prog c . step c)
          (\e => AcceptingFrom nfa (fst e) cs)
          (\e => AcceptingFrom nfa (fst e) (c :: cs))
          (runMappingSpec c)
          tds
          (recordPath nfa prog _ cs prf)
  in (x ** (isElem, satQ))

extractEvidenceFrom : {auto nfa : NA} -> {prog : Program nfa} -> (td : Thread nfa) -> AcceptingFrom nfa (fst td) word -> Evidence
extractEvidenceFrom {prog = prog} td (Accept (fst td) prf) = (snd td).evidence
extractEvidenceFrom td (Step (fst td) c t prf acc) = ?extractEvidenceFrom_rhs_1


extractEvidence : {auto nfa : NA} -> Accepting nfa word -> Evidence
