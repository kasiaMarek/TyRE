module Verification

import NFA
import Evidence
import Data.List.Elem
import Data.List
import Extra
import Syntax.PreorderReasoning

fromJust: (m: Maybe a) -> (prf: m = Just x) -> a
fromJust (Just x) Refl = x

foldLeftPrf: (xs: List a) -> (x: a) -> (f: a -> List b) -> ((x::xs >>= f) = (f x) ++ (xs >>= f))
foldLeftPrf xs x f = ?what

hereOrThereConcat: (xs: List a) -> (ys: List a) -> (elem `Elem` (xs ++ ys)) -> Either (elem `Elem` xs) (elem `Elem` ys)
hereOrThereConcat [] ys x = Right x
hereOrThereConcat (elem :: xs) ys Here = Left Here
hereOrThereConcat (y :: xs) ys (There x) =
  let tail = hereOrThereConcat xs ys x
  in case tail of
    (Left e) => Left $ There e
    (Right e) => Right e

foldElem: {a,b: Type} -> (elem : b) -> (xs: List a) -> (f: a -> List b) -> (elem `Elem` (xs >>= f))
        -> (elem' ** (elem' `Elem` xs, elem `Elem` (f elem')))
foldElem elem [] f prf = absurd prf
foldElem elem (x :: xs) f prf =
  let hereOrThere = hereOrThereConcat (f x) (xs >>= f) (replace {p=(elem `Elem`)} (foldLeftPrf _ _ _) prf)
  in case hereOrThere of
    (Left prf1) => ?k
    (Right prf1) => ?l--foldElem elem xs f prf

-- foldElem elem (x :: xs) f prf =
--   let shed = foldLeftPrf xs y f
--   in (?elem' ** (?p1, ?p2))

data AcceptingFrom : (nfa : NA) -> (s : nfa.State) -> (word : Word) -> Type where
  Accept : {auto nfa : NA} -> (s : nfa.State) -> (prf : nfa.accepting s = True) -> AcceptingFrom nfa s []
  Step   : {auto nfa : NA} -> (s : nfa.State) -> (c : Char) -> (t : nfa.State)
        -> (prf : t `Elem` (nfa.next s c))
        -> AcceptingFrom nfa t w
        -> AcceptingFrom nfa s (c :: w)

data Accepting : (nfa : NA) -> (word : Word) -> Type where
  Start : {auto nfa : NA} -> (s : nfa.State) -> (prf : s `Elem` nfa.start) -> AcceptingFrom nfa s w
       -> Accepting nfa w

recordPath : (nfa : NA) -> (prog : Program nfa)-> (tds : List (Thread nfa)) -> (str : Word)
         -> (prf : runFrom prog str tds = Just ev)
         -> (td : Thread nfa ** (td `Elem` tds, AcceptingFrom nfa (fst td) str))

recordPath nfa prog tds [] prf =
  let (x ** (_, woMap)) = mapMaybe _ _ prf
      (td ** (tdInTds, accept)) = foundImpliesExists _ _ woMap
  in (td ** (tdInTds, Accept (fst td) accept))

recordPath nfa prog tds (c :: cs) prf =
  let (td' ** (tail', accept')) = recordPath nfa prog _ cs prf
      prf1 : (td ** (td `Elem` tds, td' `Elem` (mapF (\(s,r) => (s, snd (execute (Just c) r td))) (nfa.next (fst td) c) (prog.next (fst td) c))))
  in (fst prf1 ** (fst (snd prf1), Step (fst (fst prf1)) c (fst td') ?p accept'))

extractEvidenceFrom : {auto nfa : NA} -> {prog : Program nfa} -> (td : Thread nfa) -> AcceptingFrom nfa (fst td) word -> Evidence
extractEvidenceFrom {prog} td (Accept (fst td) prf) =
  let m : Maybe Evidence
      m = runFrom prog [] [td]
      isJust : (m = Just (snd td).evidence)
      isJust = Calc $
        |~ map (\td => (snd td).evidence) (find (\td => nfa.accepting (fst td)) [td])
        ~~ map (\td => (snd td).evidence) (if (nfa.accepting (fst td)) then (Just td) else Nothing)...(cong (map (\td => .evidence (snd td))) ?w)
        ~~ (map (\td => (snd td).evidence) (Just td)) ...(?hole prf)
        ~~ (Just (snd td).evidence) ...(Refl)
  in fromJust (runFrom prog [] [td]) isJust

extractEvidenceFrom td (Step (fst td) c t prf acc) = ?extractEvidenceFrom_rhs_1


extractEvidence : {auto nfa : NA} -> Accepting nfa word -> Evidence
