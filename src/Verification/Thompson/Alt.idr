module Verification.Thompson.Alt

import Data.Vect
import Data.List
import Data.List.Elem

import Core
import NFA
import NFA.Thompson
import Verification.AcceptingPath
import Extra
import Verification.Routine
import Verification.Thompson.Concat.Extra
import Verification.Thompson.Alt.Extra
import Verification.Thompson.Alt.EqualityPrf

%default total

public export
record AltEvidencePrfLeftData  {word : Word} (re1 : CoreRE) (re2 : CoreRE)
                                  (acc: Accepting (thompson $ Alt re1 re2).nfa word) where
  constructor MkAltEvidencePrfLeftData
  word1     : Word
  acc1      : Accepting (thompson re1).nfa word1
  routineEq : (extractRoutine (thompson $ Alt re1 re2).nfa (thompson $ Alt re1 re2).prog acc =
                (extractRoutine (thompson re1).nfa (thompson re1).prog acc1 ++ [Regular EmitLeft]))

public export
record AltEvidencePrfRightData  {word : Word} (re1 : CoreRE) (re2 : CoreRE)
                                  (acc: Accepting (thompson $ Alt re1 re2).nfa word) where
  constructor MkAltEvidencePrfRightData
  word2     : Word
  acc2      : Accepting (thompson re2).nfa word1
  routineEq : (extractRoutine (thompson $ Alt re1 re2).nfa (thompson $ Alt re1 re2).prog acc =
                (extractRoutine (thompson re2).nfa (thompson re2).prog acc2 ++ [Regular EmitRight]))

public export
record AltEvLeftDataAux  {word : Word} (re1 : CoreRE) (re2 : CoreRE) {s : (thompson re1).nfa.State}
                                  (acc: AcceptingFrom (thompson $ Alt re1 re2).nfa (CTh1 s) word) where
  constructor MkAltEvLeftDataAux
  word1     : Word
  acc1      : AcceptingFrom (thompson re1).nfa s word1
  routineEq : (extractRoutineFrom {nfa =(thompson $ Alt re1 re2).nfa, prog=(thompson $ Alt re1 re2).prog} acc =
                (extractRoutineFrom {nfa = (thompson re1).nfa, prog=(thompson re1).prog} acc1 ++ [Regular EmitLeft]))

public export
record AltEvRightDataAux  {word : Word} (re1 : CoreRE) (re2 : CoreRE) {s : (thompson re2).nfa.State}
                                  (acc: AcceptingFrom (thompson $ Alt re1 re2).nfa (CTh2 s) word) where
  constructor MkAltEvRightDataAux
  word2     : Word
  acc2      : AcceptingFrom (thompson re2).nfa s word2
  routineEq : (extractRoutineFrom {nfa =(thompson $ Alt re1 re2).nfa, prog=(thompson $ Alt re1 re2).prog} acc =
                (extractRoutineFrom {nfa = (thompson re2).nfa, prog=(thompson re2).prog} acc2 ++ [Regular EmitRight]))

public export
altEvidencePrfAuxLeft : (re1 : CoreRE) -> (re2 : CoreRE) -> {s : (thompson re1).nfa.State}
                    -> (acc: AcceptingFrom (thompson $ Alt re1 re2).nfa (CTh1 s) word)
                    -> AltEvLeftDataAux re1 re2 acc

altEvidencePrfAuxLeft re1 re2 (Step (CTh1 s) c CEnd prf (Accept CEnd Refl)) =
  let sm1 : SM
      sm1 = thompson re1
      ans : CombiningTransitionsForNewData (nextFromOneAlt sm1 s c) CEnd prf
      ans = aboutCombiningTransitionsForNew (nextFromOneAlt sm1 s c) CEnd prf CTh1notEqCEnd
  in MkAltEvLeftDataAux
      [c]
      (Step {nfa = sm1.nfa} s c ans.oldState ans.oldIsElemOfOld (Accept {nfa = sm1.nfa} ans.oldState ans.oldAccepts))
        rewrite ans.routineEqualityPrf in
          rewrite (rforEnd ans.stateIsElemOfNew [EmitLeft]) in
              (cong (Observe c ::) $ endEqPrf _ _)

altEvidencePrfAuxLeft re1 re2 (Step (CTh1 s) c (CTh2 t) prf (Step (CTh2 t) c' s' prf' acc)) =
  absurd $ cTh2InstElemOfNextFromOneAlt (thompson re1) t s c prf
altEvidencePrfAuxLeft re1 re2 (Step (CTh1 s) c (CTh1 t) prf (Step (CTh1 t) c' s' prf' acc)) =
  let sm1 : SM
      sm1 = thompson re1
      rest := altEvidencePrfAuxLeft re1 re2 (Step {nfa = (thompson $ Alt re1 re2).nfa} (CTh1 t) c' s' prf' acc)
      aos : CombiningTransitionsForOldData (nextFromOneAlt sm1 s c) (CTh1 t) prf t
      aos = aboutCombiningTransitionsForOld (nextFromOneAlt sm1 s c) (CTh1 t)
                                            prf t (\x,x,Refl => Refl)
                                            Refl (ch1NotElemOFEnd t)
  in MkAltEvLeftDataAux (c::rest.word1)
      (Step {nfa = sm1.nfa} s c t (aos.oldIsElemOfOld) rest.acc1)
      (rewrite aos.routineEqualityPrf in rewrite rest.routineEq in (cong (Observe c ::) (appendAssociative _ _ _)))

public export
altEvidencePrfAuxRight : (re1 : CoreRE) -> (re2: CoreRE)
              -> {s : (thompson re2).nfa.State}
              -> (acc: AcceptingFrom (thompson $ Alt re1 re2).nfa (CTh2 s) word)
              -> AltEvRightDataAux re1 re2 acc

altEvidencePrfAuxRight re1 re2 (Step (CTh2 s) c CEnd prf (Accept CEnd Refl)) =
  let sm2 : SM
      sm2 = thompson re2
      ans : CombiningTransitionsForNewData (nextFromTwoAlt sm2 s c) CEnd prf
      ans = aboutCombiningTransitionsForNew (nextFromTwoAlt sm2 s c) CEnd prf CTh2notEqCEnd
  in MkAltEvRightDataAux
      [c]
      (Step {nfa = sm2.nfa} s c ans.oldState ans.oldIsElemOfOld (Accept {nfa = sm2.nfa} ans.oldState ans.oldAccepts))
        rewrite ans.routineEqualityPrf in
          rewrite (rforEnd ans.stateIsElemOfNew [EmitRight]) in
              (cong (Observe c ::) $ endEqPrf _ _)

altEvidencePrfAuxRight re1 re2 (Step (CTh2 s) c (CTh1 t) prf (Step (CTh1 t) c' s' prf' acc)) =
  absurd $ cTh1InstElemOfNextFromTwoAlt (thompson re2) t s c prf
altEvidencePrfAuxRight re1 re2 (Step (CTh2 s) c (CTh2 t) prf (Step (CTh2 t) c' s' prf' acc)) =
  let sm2 : SM
      sm2 = thompson re2
      rest := altEvidencePrfAuxRight re1 re2 (Step {nfa = (thompson $ Alt re1 re2).nfa} (CTh2 t) c' s' prf' acc)
      aos : CombiningTransitionsForOldData (nextFromTwoAlt sm2 s c) (CTh2 t) prf t
      aos = aboutCombiningTransitionsForOld (nextFromTwoAlt sm2 s c) (CTh2 t)
                                            prf t (\x,x,Refl => Refl)
                                            Refl (ch2NotElemOFEnd t)
  in MkAltEvRightDataAux (c::rest.word2)
      (Step {nfa = sm2.nfa} s c t (aos.oldIsElemOfOld) rest.acc2)
      (rewrite aos.routineEqualityPrf in rewrite rest.routineEq in (cong (Observe c ::) (appendAssociative _ _ _)))

public export
altEvidencePrf : (re1 : CoreRE) -> (re2: CoreRE)
                  -> (acc: Accepting (thompson $ Alt re1 re2).nfa word)
                  -> Either (AltEvidencePrfLeftData re1 re2 acc)
                            (AltEvidencePrfRightData re1 re2 acc)

altEvidencePrf re1 re2 (Start s prf acc) with (
    let sm1 : SM
        sm1 = thompson re1
        sm2 : SM
        sm2 = thompson re2
        0 state : Type
        state = CState sm1.nfa.State sm2.nfa.State
        start1 : (xs: List state ** Vect (length xs) Routine)
        start1 = combineTransitions $ initOneAlt sm1
        start2 : (xs: List state ** Vect (length xs) Routine)
        start2 = combineTransitions $ initTwoAlt sm2
    in hereOrThereExtractBasedOnFst (fst start1) (fst start2) (snd start1) (snd start2) s prf
  )

  altEvidencePrf {word = []} re1 re2 (Start CEnd prf (Accept CEnd Refl)) | (Left (pos ** eqPrf)) =
    let sm1 : SM
        sm1 = thompson re1
        ans : CombiningTransitionsForNewData (initOneAlt sm1) CEnd pos
        ans = aboutCombiningTransitionsForNew (initOneAlt sm1) CEnd pos CTh1notEqCEnd
    in Left $ MkAltEvidencePrfLeftData []
                (Start {nfa=sm1.nfa} ans.oldState ans.oldIsElemOfOld
                  (Accept {nfa=sm1.nfa} ans.oldState ans.oldAccepts))
                (rewrite eqPrf in
                  rewrite ans.routineEqualityPrf in
                    rewrite (rforEnd ans.stateIsElemOfNew [EmitLeft]) in
                    (endEqPrf _ _))

  altEvidencePrf {word = []} re1 re2 (Start CEnd prf (Accept CEnd Refl)) | (Right (pos ** eqPrf)) =
    let sm2 : SM
        sm2 = thompson re2
        ans : CombiningTransitionsForNewData (initTwoAlt sm2) CEnd pos
        ans = aboutCombiningTransitionsForNew (initTwoAlt sm2) CEnd pos CTh2notEqCEnd
    in Right $ MkAltEvidencePrfRightData []
                (Start {nfa=sm2.nfa} ans.oldState ans.oldIsElemOfOld
                  (Accept {nfa=sm2.nfa} ans.oldState ans.oldAccepts))
                (rewrite eqPrf in
                  rewrite ans.routineEqualityPrf in
                    rewrite (rforEnd ans.stateIsElemOfNew [EmitRight]) in
                    (endEqPrf _ _))

  altEvidencePrf re1 re2 (Start (CTh1 s) prf acc) | (Left (pos ** eqPrf)) =
    let sm1 : SM
        sm1 = thompson re1
        rest : AltEvLeftDataAux re1 re2 acc
        rest = altEvidencePrfAuxLeft re1 re2 acc
        aos : CombiningTransitionsForOldData (initOneAlt sm1) (CTh1 s) pos s
        aos = aboutCombiningTransitionsForOld (initOneAlt sm1) (CTh1 s)
                                              pos s (\x,x,Refl => Refl)
                                              Refl (ch1NotElemOFEnd _)
    in Left $ MkAltEvidencePrfLeftData
                rest.word1
                (Start {nfa=sm1.nfa} s aos.oldIsElemOfOld rest.acc1)
                (rewrite eqPrf in
                  rewrite aos.routineEqualityPrf in
                    rewrite rest.routineEq in
                      (appendAssociative _ _ _))

  altEvidencePrf re1 re2 (Start (CTh1 s) prf acc) | (Right (pos ** eqPrf)) =
    absurd $ cTh1InstElemOfInitTwoAlt (thompson re2) s pos

  altEvidencePrf re1 re2 (Start (CTh2 s) prf acc) | (Left (pos ** eqPrf)) =
    absurd $ cTh2InstElemOfInitOneAlt (thompson re1) s pos

  altEvidencePrf re1 re2 (Start (CTh2 s) prf acc) | (Right (pos ** eqPrf)) =
    let sm2 : SM
        sm2 = thompson re2
        rest : AltEvRightDataAux re1 re2 acc
        rest = altEvidencePrfAuxRight re1 re2 acc
        aos : CombiningTransitionsForOldData (initTwoAlt sm2) (CTh2 s) pos s
        aos = aboutCombiningTransitionsForOld (initTwoAlt sm2) (CTh2 s)
                                              pos s (\x,x,Refl => Refl)
                                              Refl (ch2NotElemOFEnd _)
    in Right $ MkAltEvidencePrfRightData
                rest.word2
                (Start {nfa=sm2.nfa} s aos.oldIsElemOfOld rest.acc2)
                (rewrite eqPrf in
                  rewrite aos.routineEqualityPrf in
                    rewrite rest.routineEq in
                      (appendAssociative _ _ _))
