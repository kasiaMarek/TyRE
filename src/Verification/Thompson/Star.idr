module Verification.Thompson.Star

import Data.Vect
import Data.List
import Data.List.Elem
import Data.SnocList
import Data.SnocList.Extra

import Core
import NFA
import NFA.Thompson
import Verification.AcceptingPath
import Extra
import Verification.Routine
import Evidence
import Verification.Thompson.Star.EqualityPrf
import Verification.Thompson.Extra
import Verification.Thompson.Star.Extra

startEvidencePrfAux: (re : CoreRE)
                    -> (s : (thompson re).nfa.State)
                    -> {s': (thompson $ Star re).nfa.State}
                    -> (acc : AcceptingFrom (thompson $ Star re).nfa s' word)
                    -> (Either (s' = (CTh1 s)) (s' = (CTh2 s)))
                    -> (currWord : Word **
                          (currAcc : AcceptingFrom (thompson re).nfa s currWord **
                            (accs : List (w : Word ** Accepting (thompson re).nfa w) **
                              (extractRoutineFrom {nfa = (thompson $ Star re).nfa} {prog = (thompson $ Star re).prog} acc
                                = extractRoutineFrom {nfa = (thompson re).nfa} {prog = (thompson re).prog} currAcc
                                    ++ (accs >>= (\ac => extractRoutine (thompson re).nfa (thompson re).prog (snd ac)))
                                      ++ [Regular EmitBList]))))


startEvidencePrfAux {s' = (CTh1 s)} re s (Step (CTh1 s) c CEnd prf (Accept CEnd Refl)) (Left Refl) =
  let sm : SM
      sm = thompson re
      (MkCombiningTransitionsForNewData
        t tInNext cEndInAdded tAccepts rEqPrf) :=
          aboutCombiningTransitionsForNew (nextStarData sm s c) CEnd prf CTh1notEqCEnd
  in case cEndInAdded of
        (There x) => absurd (CEndIsElemOfMapCTh2 _ x)
        Here =>
          ([c] ** (Step {nfa = sm.nfa} s c t tInNext (Accept {nfa = sm.nfa} t tAccepts) **
            ([] ** rewrite rEqPrf in (cong (Observe c ::) (starEq0 _)))))

startEvidencePrfAux {s' = (CTh1 s)} re s (Step (CTh1 s) c (CTh2 t) prf acc) (Left Refl) =
  let sm : SM
      sm = thompson re
      (currWord ** (currAcc ** (accs ** eqPrf))) := startEvidencePrfAux re t acc (Right Refl)
      (MkCombiningTransitionsForNewData
        u uInNext cTh2InAdded uAccepts rEqPrf) :=
          aboutCombiningTransitionsForNew (nextStarData sm s c) (CTh2 t) prf CTh2notEqCTh1
      (tInStart ** rEq) := routineForStartRep sm cTh2InAdded
      newAcc : (w : Word ** Accepting sm.nfa w)
      newAcc = (currWord ** Start {nfa = sm.nfa} t tInStart currAcc)
  in ([c] ** (Step {nfa = sm.nfa} s c u uInNext (Accept {nfa = sm.nfa} u uAccepts) **
        (newAcc::accs **
          rewrite foldLeftIsConcatPrf accs newAcc ((\ac => extractRoutine sm.nfa sm.prog (snd ac))) in
            rewrite eqPrf in rewrite rEqPrf in rewrite rEq in
              cong (Observe c ::) (starEq1 _ _ _ _ _))))

startEvidencePrfAux {s' = (CTh1 s)} re s (Step (CTh1 s) c (CTh1 t) prf acc) (Left Refl) =
  let sm : SM
      sm = thompson re
      (currWord ** (currAcc ** (accs ** eqPrf))) := startEvidencePrfAux re t acc (Left Refl)
      (MkCombiningTransitionsForOldData oldIsElemOfOld routineEqualityPrf) :=
        aboutCombiningTransitionsForOld (nextStarData sm s c) (CTh1 t)
                                        prf t (\_,_,Refl => Refl) Refl
                                        (\(There pos) => CTh1IsElemOfMapCTh2 _ pos)

  in (c::currWord ** (Step {nfa = sm.nfa} s c t oldIsElemOfOld currAcc **
          (accs ** rewrite routineEqualityPrf in rewrite eqPrf in
                cong (Observe c ::) (appendAssociative _ _ _))))

startEvidencePrfAux {word} re s acc (Right prf) with (prf)
  startEvidencePrfAux {s' = (CTh2 s)} {word = c::_} re s (Step (CTh2 s) c CEnd prf (Accept CEnd Refl)) (Right Refl) | Refl =
    let sm : SM
        sm = thompson re
        (MkCombiningTransitionsForNewData
          t tInNext cEndInAdded tAccepts rEqPrf) :=
            aboutCombiningTransitionsForNew (nextStarData sm s c) CEnd prf CTh1notEqCEnd
    in case cEndInAdded of
          (There x) => absurd (CEndIsElemOfMapCTh2 _ x)
          Here =>
            ([c] ** (Step {nfa = sm.nfa} s c t tInNext (Accept {nfa = sm.nfa} t tAccepts) **
              ([] ** rewrite rEqPrf in (cong (Observe c ::) (starEq0 _)))))

  startEvidencePrfAux {s' = (CTh2 s)} {word = c::_} re s (Step (CTh2 s) c (CTh2 t) prf acc) (Right Refl) | Refl =
    let sm : SM
        sm = thompson re
        (currWord ** (currAcc ** (accs ** eqPrf))) := startEvidencePrfAux re t acc (Right Refl)
        (MkCombiningTransitionsForNewData
          u uInNext cTh2InAdded uAccepts rEqPrf) :=
            aboutCombiningTransitionsForNew (nextStarData sm s c) (CTh2 t) prf CTh2notEqCTh1
        (tInStart ** rEq) := routineForStartRep sm cTh2InAdded
        newAcc : (w : Word ** Accepting sm.nfa w)
        newAcc = (currWord ** Start {nfa = sm.nfa} t tInStart currAcc)
    in ([c] ** (Step {nfa = sm.nfa} s c u uInNext (Accept {nfa = sm.nfa} u uAccepts) **
          (newAcc::accs **
            rewrite foldLeftIsConcatPrf accs newAcc ((\ac => extractRoutine sm.nfa sm.prog (snd ac))) in
              rewrite eqPrf in rewrite rEqPrf in rewrite rEq in
                cong (Observe c ::) (starEq1 _ _ _ _ _))))

  startEvidencePrfAux {s' = (CTh2 s)} {word = c::_} re s (Step (CTh2 s) c (CTh1 t) prf acc) (Right Refl) | Refl =
    let sm : SM
        sm = thompson re
        (currWord ** (currAcc ** (accs ** eqPrf))) := startEvidencePrfAux re t acc (Left Refl)
        (MkCombiningTransitionsForOldData oldIsElemOfOld routineEqualityPrf) :=
          aboutCombiningTransitionsForOld (nextStarData sm s c) (CTh1 t)
                                          prf t (\_,_,Refl => Refl) Refl
                                          (\(There pos) => CTh1IsElemOfMapCTh2 _ pos)

    in (c::currWord ** (Step {nfa = sm.nfa} s c t oldIsElemOfOld currAcc **
            (accs ** rewrite routineEqualityPrf in rewrite eqPrf in
                  cong (Observe c ::) (appendAssociative _ _ _))))

export
starEvidencePrf : (re : CoreRE)
                -> (acc : Accepting (thompson $ Star re).nfa word)
                -> (accs : List (w : Word ** Accepting (thompson re).nfa w)
                      ** (extractRoutine (thompson $ Star re).nfa (thompson $ Star re).prog acc
                            = (Regular EmitEList) ::
                            (accs >>= (\ac => extractRoutine (thompson re).nfa (thompson re).prog (snd ac)))
                              ++ [Regular EmitBList]))

starEvidencePrf re (Start CEnd (There pos) acc)  = absurd (CEndIsElemOfMapCTh2 _ pos)
starEvidencePrf re (Start (CTh1 s) (There pos) acc) = absurd (CTh1IsElemOfMapCTh2 _ pos)
starEvidencePrf re (Start CEnd      Here         (Accept CEnd Refl))  = ([] ** Refl)
starEvidencePrf re (Start (CTh2 s)  pos          acc)                 =
  let sm : SM
      sm = thompson re
      (currWord ** (currAcc ** (accs ** eqPrf))) := startEvidencePrfAux re s acc (Right Refl)
      (sInStart ** rEq) := routineForStart sm pos
      newAcc : (w : Word ** Accepting sm.nfa w)
      newAcc = (currWord ** Start {nfa = sm.nfa} s sInStart currAcc)
  in (newAcc::accs **
          rewrite foldLeftIsConcatPrf accs newAcc ((\ac => extractRoutine sm.nfa sm.prog (snd ac))) in
            rewrite eqPrf in rewrite rEq in
              cong (Regular EmitEList ::) (appendAssociative4 _ _ _ _))
