module Evidence

import Codes
import Data.SnocList
import Data.SnocList.Elem
import Data.SnocList.Extra
import Data.List

%default total

public export
data EvidenceMarker =
   PairMark
 | CharMark Char
 | GroupMark (SnocList Char)
 | LeftBranchMark
 | RightBranchMark
 | UnitMark

public export
Evidence : Type
Evidence = SnocList EvidenceMarker

public export
data Encodes : Evidence -> SnocList Code -> Type where
  Lin : [<] `Encodes` [<]
  AChar
    : (prf : evs `Encodes` cs)
    -> (c : Char)
    -> (evs :< CharMark c) `Encodes` cs :< CharC
  APair
    : (prf : evs `Encodes` cs)
   -> (prf1 : ev1 `Encodes` [< c1])
   -> (prf2 : ev2 `Encodes` [< c2])
   -> {auto ford : evs' = evs ++ ev1 ++ ev2}
   -> (evs' :< PairMark) `Encodes` (cs :< PairC c1 c2)
  AGroup
    : (prf : evs `Encodes` cs)
    -> (str : SnocList Char)
    -> (evs :< GroupMark str) `Encodes` cs :< StringC
  ALeft
    : (prf : evs `Encodes` cs)
    -> (prf1 : ev1 `Encodes` [< c1])
    -> (c2 : Code)
    -> {auto ford : evs' = evs ++ ev1}
    -> (evs' :< LeftBranchMark) `Encodes` (cs :< EitherC c1 c2)
  ARight
    : (prf : evs `Encodes` cs)
    -> (prf2 : ev2 `Encodes` [< c2])
    -> (c1 : Code)
    -> {auto ford : evs' = evs ++ ev2}
    -> (evs' :< RightBranchMark) `Encodes` (cs :< EitherC c1 c2)
  AnEmpty
    : (prf : evs `Encodes` cs)
    -> (evs :< UnitMark) `Encodes` cs :< UnitC


record Result (ev : Evidence) (c : Code) (cs : SnocList Code) where
  constructor MkResult
  result : Sem c
  rest   : Evidence
  0 restValid : rest `Encodes` cs

recontextualise : (prf1 : evs1 `Encodes` cs1)
              -> (prf2 : evs2 `Encodes` cs2)
              -> (evs1 ++ evs2) `Encodes` (cs1 ++ cs2)

recontextualise prf1 [<] = prf1

recontextualise prf1 (AGroup prf str) = AGroup (recontextualise prf1 prf) str

recontextualise prf1 (APair {ford = eqprf} prf prf2' prf1') =
  APair (recontextualise prf1 prf) prf2' prf1'
      {ford = trans (cong (evs1 ++) eqprf) appendAssociative}

recontextualise prf1 (AChar prf c) = AChar (recontextualise prf1 prf) c

recontextualise prf1 (ALeft {ford, ev1, evs} prf prf1' c2) =
  ALeft (recontextualise prf1 prf) prf1' c2
    {ford = trans (cong (evs1 ++) ford) appendAssociative}

recontextualise prf1 (ARight {ford, ev2, evs} prf prf2 c1) =
  ARight (recontextualise prf1 prf) prf2 c1
    {ford = trans (cong (evs1 ++) ford) appendAssociative}

recontextualise prf1 (AnEmpty prf) = AnEmpty (recontextualise prf1 prf)

extractResultAuxChar : (ev : Evidence) -> (0 prf : ev `Encodes` (cs :< c))
                    -> (0 prf1 : prf = AChar prf' c')
                    -> Result ev c cs

extractResultAuxChar (evs :< CharMark c') (AChar prf' c') Refl = MkResult c' evs prf'

extractResult : (ev : Evidence) -> (0 prf : ev `Encodes` (cs :< c)) -> Result ev c cs

extractResult (evs :< CharMark c') (AChar prf c') = MkResult c' evs prf

extractResult (e@(evs ++ (ev1 ++ ev2)) :< PairMark) (APair {cs, c1, c2, ford=Refl} prf prf1 prf2) =
  let   0 prf1' = recontextualise (recontextualise prf prf1) prf2
        0 eqprf = sym (trans Refl appendAssociative)
        0 prf'  = replace {p=(\x => x `Encodes` (cs :< c1 :< c2))} eqprf prf1'
        result2 = extractResult e prf'
        result1 = extractResult result2.rest (result2.restValid)
  in MkResult (result1.result, result2.result) result1.rest result1.restValid

extractResult (evs :< (GroupMark sx)) (AGroup prf sx) = MkResult (pack $ reverse $ asList sx) evs prf

extractResult (e@(evs ++ ev) :< LeftBranchMark) (ALeft {ford = Refl} prf prf1 c2) =
  let result = extractResult e (recontextualise prf prf1)
  in MkResult (Left result.result) result.rest result.restValid

extractResult (e@(evs ++ ev) :< RightBranchMark) (ARight {ford = Refl} prf prf2 c1) =
  let result = extractResult e (recontextualise prf prf2)
  in MkResult (Right result.result) result.rest result.restValid

extractResult (evs :< UnitMark) (AnEmpty prf) = MkResult () evs prf

public export
extract : (ev : Evidence) -> (0 prf : ev `Encodes` [< c]) -> Sem c
extract ev prf = (extractResult ev prf).result
