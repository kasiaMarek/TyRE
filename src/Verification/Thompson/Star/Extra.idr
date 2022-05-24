module Verification.Thompson.Star.Extra

import Data.Vect
import Data.List
import Data.List.Elem

import NFA
import NFA.Thompson

export
CEndIsElemOfMapCTh2 : (xs: List a) -> (Not $ CEnd `Elem` map CTh2 xs)
CEndIsElemOfMapCTh2 [] Here impossible
CEndIsElemOfMapCTh2 [] (There _) impossible
CEndIsElemOfMapCTh2 (x :: xs) (There pos) = CEndIsElemOfMapCTh2 xs pos

export
CTh1IsElemOfMapCTh2 : (xs: List a) -> (Not $ (CTh1 s) `Elem` map CTh2 xs)
CTh1IsElemOfMapCTh2 [] Here impossible
CTh1IsElemOfMapCTh2 [] (There _) impossible
CTh1IsElemOfMapCTh2 (x :: xs) (There pos) = CTh1IsElemOfMapCTh2 xs pos

export
routineForStartRep : (sm : SM) -> {s : sm.nfa.State} -> (prf: CTh2 s `Elem` (startStar sm))
                -> (prf1 : s `Elem` sm.nfa.start **
                      extractBasedOnFst (startStar sm) (rStartStar sm) prf =
                        extractBasedOnFst sm.nfa.start sm.prog.init prf1)

routineForStartRep sm (There pos) with (sm.prog.init)
  routineForStartRep sm (There pos) | init with (sm.nfa.start)
    routineForStartRep sm (There Here) | [] | [] impossible
    routineForStartRep sm (There (There _)) | [] | [] impossible
    routineForStartRep sm (There Here) | (y :: ys) | (x :: xs) = (Here ** Refl)
    routineForStartRep sm (There (There z)) | (y :: ys) | (x :: xs) =
      let (rPos ** prf) := (routineForStartRep sm (There z) | ys | xs)
      in (There rPos ** prf)

hPrf : (sm : SM) -> {s : CState sm.nfa.State sm.nfa.State} -> (pos: s `Elem` (startStar sm))
    -> (extractBasedOnFst (startStar sm) (initStar sm) pos =
          EmitEList :: extractBasedOnFst (startStar sm) (rStartStar sm) pos)
hPrf sm pos = extractBasedOnFstMapEq (startStar sm) (rStartStar sm) _ pos

export
routineForStart : (sm : SM) -> {s : sm.nfa.State} -> (prf: CTh2 s `Elem` (startStar sm))
                -> (prf1 : s `Elem` sm.nfa.start **
                      extractBasedOnFst (startStar sm) (initStar sm) prf =
                        EmitEList :: extractBasedOnFst sm.nfa.start sm.prog.init prf1)

routineForStart sm pos =
  let (p ** eqPrf) := routineForStartRep sm pos
  in (p ** rewrite (hPrf sm pos) in (cong (EmitEList ::) eqPrf))
