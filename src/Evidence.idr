module Evidence

import Codes
import Data.SnocList
import Data.SnocList.Elem

%default total

data EvidenceMarker =
   -- StringMark String
   PairMark
 | CharMark Char
 | GroupMark (SnocList Char)
 -- | LeftBranchMark
 -- | RightBranchMark
 -- | StarMark

Evidence : Type
Evidence = SnocList EvidenceMarker

data Encodes : Evidence -> SnocList Code -> Type where
  Lin : [<] `Encodes` [<]
  -- OnlyString
  --   : (prf : evs `Encodes` cs) -> (str : String)
  --   -> (evs :< StringMark str) `Encodes` cs :< StringC
  AChar
    : (prf : evs `Encodes` cs)
    -> (c : Char)
    -> (evs :< CharMark c) `Encodes` cs :< CharC
  APair
    : (prf : evs `Encodes` cs)
   -> (prf1 : ev1 `Encodes` [< c1])
   -> (prf2 : ev2 `Encodes` [< c2])
   -> {auto ford : evs' = (evs ++ ev1 ++ ev2) :< PairMark}
   -> evs' `Encodes` (cs :< PairC c1 c2)
  AGroup
    : (prf : evs `Encodes` cs)
    -> (str : SnocList Char)
    -> (evs :< GroupMark str) `Encodes` cs :< StringC


record Result (ev : Evidence) (c : Code) (cs : SnocList Code) where
  constructor MkResult
  result : Sem c
  rest   : Evidence
  0 restValid : rest `Encodes` cs


assoc : {a : Type} -> {x,y,z : SnocList a} -> x ++ (y ++ z) = (x ++ y) ++ z
assoc {x, y, z=[<]} = Refl
assoc {x, y, z=(sz :< z')} = cong (:< z') (assoc {x, y, z=sz})


recontextualise : (prf1 : evs1 `Encodes` cs1)
              -> (prf2 : evs2 `Encodes` cs2)
              -> (evs1 ++ evs2) `Encodes` (cs1 ++ cs2)

recontextualise prf1 [<] = prf1

recontextualise prf1 (AGroup prf str) = AGroup (recontextualise prf1 prf) str

recontextualise prf1 (APair {ford = eqprf} prf prf2' prf1') =
  let 0 p: ((evs1 ++ (evs ++ (ev1 ++ ev2))) :< PairMark = ((evs1 ++ evs) ++ (ev1 ++ ev2)) :< PairMark)
      p = cong (:< PairMark) (assoc)
  in APair (recontextualise prf1 prf) prf2' prf1'
      {ford = trans (cong (evs1 ++) eqprf) p}

recontextualise prf1 (AChar prf c) = AChar (recontextualise prf1 prf) c


extractResult : (ev : Evidence) -> (0 prf : ev `Encodes` (cs :< c)) -> Result ev c cs

extractResult (evs :< CharMark x) (AChar prf x) = MkResult x evs prf

extractResult [<] (APair _ _ _) impossible

extractResult (e@(evs ++ (ev1 ++ ev2)) :< PairMark) (APair {cs, c1, c2, ford=Refl} prf prf1 prf2) =
  let   0 prf1' = recontextualise (recontextualise prf prf1) prf2
        0 eqprf = sym (trans Refl assoc)
        0 prf'  = replace {p=(\x => x `Encodes` (cs :< c1 :< c2))} eqprf prf1'
        result2 = extractResult e prf'
        result1 = extractResult result2.rest (result2.restValid)
  in MkResult (result1.result, result2.result) result1.rest result1.restValid

extractResult (evs :< GroupMark str) (AGroup prf str) =
  let string = (reverse (pack (asList str)))
  in MkResult string evs prf


extract : (ev : Evidence) -> (0 prf : ev `Encodes` [< c]) -> Sem c
extract ev prf = (extractResult ev prf).result
