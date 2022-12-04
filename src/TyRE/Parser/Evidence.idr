module TyRE.Parser.Evidence

import Data.SnocList
import Data.SnocList.Elem
import Data.List
import Data.Nat
import Control.Order

import TyRE.Codes
import TyRE.Extra

import Syntax.PreorderReasoning.Generic

%default total

public export
data EvidenceMarker =
   PairMark
 | CharMark Char
 | GroupMark (SnocList Char)
 | LeftBranchMark
 | RightBranchMark
 | UnitMark
 | BList
 | EList

public export
Show EvidenceMarker where
  show PairMark = "PairMark"
  show (CharMark c) = "CharMark " ++ cast c
  show (GroupMark sx) = "GroupMark " ++ show sx
  show LeftBranchMark = "LeftBranchMark"
  show RightBranchMark = "RightBranchMark"
  show UnitMark = "UnitMark"
  show BList = "BList"
  show EList = "EList"

public export
Evidence : Type
Evidence = SnocList EvidenceMarker

public export
data Encodes : Evidence -> SnocList (Either () Code) -> Type where
  Lin : [<] `Encodes` [<]
  AnBegMark
    : (prf : evs `Encodes` cs)
    -> (evs :< BList) `Encodes` cs :< Left ()
  AChar
    : (prf : evs `Encodes` cs)
    -> (c : Char)
    -> (evs :< CharMark c) `Encodes` cs :< (Right CharC)
  APair
    : (prf : evs `Encodes` cs)
    -> (prf1 : ev1 `Encodes` [< Right c1])
    -> (prf2 : ev2 `Encodes` [< Right c2])
    -> {auto ford : evs' = evs ++ ev1 ++ ev2}
    -> (evs' :< PairMark) `Encodes` (cs :< (Right $ PairC c1 c2))
  AGroup
    : (prf : evs `Encodes` cs)
    -> (str : SnocList Char)
    -> (evs :< GroupMark str) `Encodes` cs :< (Right StringC)
  ALeft
    : (prf : evs `Encodes` cs)
    -> (prf1 : ev1 `Encodes` [< Right c1])
    -> (c2 : Code)
    -> {auto ford : evs' = evs ++ ev1}
    -> (evs' :< LeftBranchMark) `Encodes` (cs :< (Right $ EitherC c1 c2))
  ARight
    : (prf : evs `Encodes` cs)
    -> (prf2 : ev2 `Encodes` [< Right c2])
    -> (c1 : Code)
    -> {auto ford : evs' = evs ++ ev2}
    -> (evs' :< RightBranchMark) `Encodes` (cs :< (Right $ EitherC c1 c2))
  AnEmpty
    : (prf : evs `Encodes` cs)
    -> (evs :< UnitMark) `Encodes` cs :< (Right UnitC)
  ARepetiton
    : (prf : evs `Encodes` cs)
    -> (prf1 : evss `Encodes` (replicate n (Right c)))
    -> {auto ford: ev' = evs :< BList ++ evss}
    -> (ev' :< EList) `Encodes` (cs :< (Right (ListC c)))


record Result (ev : Evidence) (c : Code) (cs : SnocList (Either () Code)) where
  constructor MkResult
  result : Sem c
  rest : Evidence
  0 restValid : rest `Encodes` cs
  0 bound : length rest `LT` length ev

export
recontextualise : (prf1 : evs1 `Encodes` cs1)
                -> (prf2 : evs2 `Encodes` cs2)
                -> (evs1 ++ evs2) `Encodes` (cs1 ++ cs2)

recontextualise prf1 [<] = prf1

recontextualise prf1 (AGroup prf str) = AGroup (recontextualise prf1 prf) str

recontextualise prf1 (APair {ford = eqprf} prf prf2' prf1') =
  APair (recontextualise prf1 prf) prf2' prf1'
      {ford = trans (cong (evs1 ++) eqprf) (appendAssociative _ _ _)}

recontextualise prf1 (AChar prf c) = AChar (recontextualise prf1 prf) c

recontextualise prf1 (ALeft {ford, ev1, evs} prf prf1' c2) =
  ALeft (recontextualise prf1 prf) prf1' c2
    {ford = trans (cong (evs1 ++) ford) (appendAssociative _ _ _)}

recontextualise prf1 (ARight {ford, ev2, evs} prf prf2 c1) =
  ARight (recontextualise prf1 prf) prf2 c1
    {ford = trans (cong (evs1 ++) ford) (appendAssociative _ _ _)}

recontextualise prf1 (AnEmpty prf) = AnEmpty (recontextualise prf1 prf)

recontextualise prf1 (AnBegMark prf) = AnBegMark (recontextualise prf1 prf)

recontextualise prf1 (ARepetiton {ford} prf prf') =
  ARepetiton (recontextualise prf1 prf) prf'
    {ford = trans (cong (evs1 ++) ford) (appendAssociative _ _ _)}

total
helper : (0 prf : [<] `Encodes` (cs :< (Left ()) ++ (replicate n (Right c))))
      -> Void
helper (AnBegMark prf) impossible
helper (AChar prf x) impossible
helper (APair prf prf1 prf2) impossible
helper (AGroup prf str) impossible
helper (ALeft prf prf1 c2) impossible
helper (ARight prf prf2 c1) impossible
helper (AnEmpty prf) impossible
helper (ARepetiton prf prf1) impossible

{- We'll use these mutually-recursive definitions -}
total
extractRepRecSucc
  : (ev : Evidence)
  -> (0 n : Nat)
  -> (0 prff : n = (S k))
  -> (0 prf : ev `Encodes` (cs :< (Left ()) ++ (replicate n (Right c))))
  -> (0 fuel : Nat) -> (0 enough : length ev `LTE` fuel)
  -> (0 fuelIsSucc : IsSucc fuel)
  -> Result ev (ListC c) cs

total
extractRepRecAux
  : (ev : Evidence)
  -> (0 prf : ev `Encodes` (cs :< (Left ()) ++ (replicate n (Right c))))
  -> (0 prf1 : ev = ev' :< e)
  -> (0 prf2 : e = BList -> Void)
  -> (0 fuel : Nat) -> (0 enough : length ev `LTE` fuel)
  -> Result ev (ListC c) cs

total
extractRepRec
  : (ev : Evidence)
  -> (0 prf : ev `Encodes` (cs :< (Left ()) ++ (replicate n (Right c))))
  -> (0 fuel : Nat) -> (0 enough : length ev `LTE` fuel)
  -> Result ev (ListC c) cs

total
extractResult : (ev : Evidence) -> (0 prf : ev `Encodes` (cs :< (Right c)))
              -> (0 fuel : Nat) -> (0 enough : length ev `LTE` fuel)
              -> Result ev c cs

-- Implementations --

extractRepRecAux x@(ev' :< e) {n} prf Refl prf2 (S fuel) (LTESucc enough) =
  let 0 eqPrf : (k ** n = (S k))
      eqPrf = case n of
                    0 => case prf of
                          (AnBegMark x) => absurd (prf2 Refl)
                    (S k) => (k ** Refl)
  in extractRepRecSucc x n (snd eqPrf) prf (S fuel) (LTESucc enough) ItIsSucc

extractRepRec [<] prf fuel enough = absurd (helper prf)
extractRepRec sx'@(sx :< PairMark       ) prf fuel enough  = extractRepRecAux sx' prf Refl (\case _ impossible) fuel enough
extractRepRec sx'@(sx :< (CharMark x   )) prf fuel enough  = extractRepRecAux sx' prf Refl (\case _ impossible) fuel enough
extractRepRec sx'@(sx :< (GroupMark sy )) prf fuel enough  = extractRepRecAux sx' prf Refl (\case _ impossible) fuel enough
extractRepRec sx'@(sx :< LeftBranchMark ) prf fuel enough  = extractRepRecAux sx' prf Refl (\case _ impossible) fuel enough
extractRepRec sx'@(sx :< RightBranchMark) prf fuel enough  = extractRepRecAux sx' prf Refl (\case _ impossible) fuel enough
extractRepRec sx'@(sx :< UnitMark       ) prf fuel enough  = extractRepRecAux sx' prf Refl (\case _ impossible) fuel enough
extractRepRec sx'@(sx :< EList          ) prf fuel enough  = extractRepRecAux sx' prf Refl (\case _ impossible) fuel enough
extractRepRec sx'@(sx :< BList          ) {n, c} prf fuel enough =
  let 0 eqPrf : (Extra.replicate n (Right c) = [<])
      eqPrf = case n of
                0 => Refl
                (S k) => case prf of {_ impossible}
  in MkResult [<] sx
              (case (replace
                      {p=(\r => (sx :< BList) `Encodes` (cs :< (Left ()) ++ r))}
                        eqPrf prf) of
                      (AnBegMark prf') => prf')
              (reflexive {rel = LTE})

extractRepRecSucc ev {c} (S k) Refl prf (S fuel) enough ItIsSucc =
  let res  = extractResult ev prf (S fuel) enough
      rest = extractRepRec res.rest res.restValid fuel
             $ fromLteSucc
             $ CalcWith {leq = LTE} $
             |~ 1 + length res.rest
             <~ length ev ...(res.bound)
             <~ 1 + fuel  ...(enough)
  in MkResult (rest.result :< res.result) rest.rest rest.restValid
     $ CalcWith {leq = LTE} $
     |~ 1 + (length rest.rest)
     <~ 1 + (1 + (length rest.rest)) ... (plusLteMonotoneLeft 1 _ _ $
                                          lteSuccRight $ reflexive {rel = LTE})
     <~ 1 + (length res.rest) ...(plusLteMonotoneLeft 1 _ _ rest.bound)
     <~ length ev ...(res.bound)

extractResult (evs :< CharMark c') (AChar prf c') (S fuel) (LTESucc enough) =
  MkResult c' evs prf (reflexive {rel = LTE})

extractResult (e@(evs ++ (ev1 ++ ev2)) :< PairMark)
              (APair {cs, c1, c2, ford=Refl} prf prf1 prf2)
              (S fuel) (LTESucc enough) =
  let   0 prf1' = recontextualise (recontextualise prf prf1) prf2
        0 eqprf = sym (trans Refl (appendAssociative _ _ _))
        0 prf'  = replace
                  {p=(\x => x `Encodes` (cs :< (Right c1) :< (Right  c2)))}
                  eqprf prf1'
        result2 = extractResult e prf' fuel enough
        result1 = extractResult result2.rest (result2.restValid) fuel
                   $ fromLteSucc
                   $ CalcWith {leq = LTE} $
                    |~ 1 + length result2.rest
                    <~ length (evs ++ (ev1 ++ ev2)) ...(result2.bound)
                    <~ fuel ...(enough)
                    <~ 1 + fuel ...(lteSuccRight (reflexive {rel = LTE}))
  in MkResult (result1.result, result2.result) result1.rest result1.restValid
    $ CalcWith {leq = LTE} $
      |~ 1 + length result1.rest
      <~ length result2.rest ...(result1.bound)
      <~ length e ...(lteSuccLeft result2.bound)
      <~ 1 + length e ...(lteSuccRight (reflexive {rel = LTE}))

extractResult (evs :< (GroupMark sx)) (AGroup prf sx) (S fuel) (LTESucc enough) =
  MkResult (pack $ reverse $ asList sx) evs prf (reflexive {rel = LTE})

extractResult (e@(evs ++ ev) :< LeftBranchMark)
              (ALeft {ford = Refl} prf prf1 c2) (S fuel) (LTESucc enough) =
  let result = extractResult e (recontextualise prf prf1) fuel enough
  in MkResult (Left result.result) result.rest result.restValid
    $ CalcWith {leq = LTE} $
      |~ 1 + length result.rest
      <~ length (evs ++ ev) ...(result.bound)
      <~ 1 + length (evs ++ ev) ...(lteSuccRight (reflexive {rel = LTE}))

extractResult (e@(evs ++ ev) :< RightBranchMark)
              (ARight {ford = Refl} prf prf2 c1) (S fuel) (LTESucc enough) =
  let result = extractResult e (recontextualise prf prf2) fuel enough
  in MkResult (Right result.result) result.rest result.restValid
    $ CalcWith {leq = LTE} $
      |~ 1 + length result.rest
      <~ length (evs ++ ev) ...(result.bound)
      <~ 1 + length (evs ++ ev) ...(lteSuccRight (reflexive {rel = LTE}))

extractResult (evs :< UnitMark) (AnEmpty prf) (S fuel) (LTESucc enough) =
  MkResult () evs prf (reflexive {rel = LTE})

extractResult (evs :< EList)
              (ARepetiton {ford, n} prf prf1) (S fuel) (LTESucc enough) =
  let res = extractRepRec evs
        (rewrite ford in (recontextualise (AnBegMark prf) prf1)) fuel enough
  in MkResult res.result res.rest res.restValid
  $ CalcWith {leq = LTE} $
    |~ 1 + length res.rest
    <~ length evs ...(res.bound)
    <~ 1 + length evs ...(lteSuccRight (reflexive {rel = LTE}))

----------------------------------------------------

public export
extract : (ev : Evidence) -> (0 prf : ev `Encodes` [< Right c]) -> Sem c
extract ev prf =
  (extractResult ev prf (length ev) (reflexive {rel = LTE})).result
