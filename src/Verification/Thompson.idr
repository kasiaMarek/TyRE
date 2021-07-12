module Verification.Thompson

import NFA
import NFA.Thompson
import Evidence
import Verification.AcceptingPath
import Extra
import Data.List
import Core
import Codes
import Data.SnocList
import Data.SnocList.Extra
import Verification.Routine
import Data.List.Elem
import Verification.Thompson.Group
import Data.Vect
import Extra.Reflects
import Verification.Thompson.Concat
import Verification.Thompson.Alt
import Verification.Thompson.Concat.EqualityPrf
import Verification.Thompson.Alt.EqualityPrf

thompsonRoutinePrf : (re : CoreRE)
                  -> (acc : Accepting (thompson re).nfa word)
                  -> (mcvm  : (Maybe Char, VMState))
                  -> (ev  : Evidence
                        ** (executeRoutineFrom (extractRoutine (thompson re).nfa (thompson re).prog acc) mcvm
                              = (snd mcvm).evidence ++ ev, ev `Encodes` [< ShapeCode re]))

thompsonRoutinePrf (Pred f) (Start s (There prf) x) mcvm = absurd prf
thompsonRoutinePrf {word = []} (Pred f) (Start StartState Here (Accept StartState prf)) mcvm = absurd prf
thompsonRoutinePrf {word = c::_} (Pred f) (Start StartState Here (Step StartState c t prf acc)) mcvm with (f c)
  thompsonRoutinePrf {word = c::_} (Pred f) (Start StartState Here (Step StartState c t prf acc)) mcvm | False = absurd prf
  thompsonRoutinePrf {word = c::_} (Pred f) (Start StartState Here (Step StartState c t (There prf) acc)) mcvm | True = absurd prf
  thompsonRoutinePrf {word = c::c'::_} (Pred f) (Start StartState Here (Step StartState c AcceptState Here (Step AcceptState c' t prf acc))) mcvm | True = absurd prf
  thompsonRoutinePrf {word = [c]} (Pred f) (Start StartState Here (Step StartState c AcceptState Here (Accept AcceptState Refl))) (mc, vm) | True = ([< CharMark c] ** (Refl, AChar [<] c))

thompsonRoutinePrf Empty (Start EndState Here (Accept EndState Refl)) (mc, vm) = ([< UnitMark] ** (Refl, AnEmpty [<]))

thompsonRoutinePrf (Concat re1 re2) acc mcvm =
  let p : ConcatEvidencePrfData re1 re2 acc
      p = concatEvidencePrf re1 re2 acc
      exr1 : ExtendedRoutine
      exr1 = extractRoutine (thompson re1).nfa (thompson re1).prog p.acc1
      exr2 : ExtendedRoutine
      exr2 = extractRoutine (thompson re2).nfa (thompson re2).prog p.acc2
      (ev1 ** (eq1, encodes1)) := thompsonRoutinePrf re1 p.acc1 mcvm
      vmmc' : (Maybe Char, VMState)
      vmmc' = executeRoutineSteps exr1 mcvm
      (ev2 ** (eq2, encodes2)) := thompsonRoutinePrf re2 p.acc2 vmmc'

      routineEquality : ((snd $ executeRoutineSteps (exr1 ++ exr2 ++ [Regular EmitPair]) mcvm).evidence
                            = (snd $ executeRoutineSteps exr2 (executeRoutineSteps exr1 mcvm)).evidence :< PairMark)
      routineEquality = concatRoutinePrf exr1 exr2 mcvm
      encodes : (((ev1 ++ ev2) :< PairMark) `Encodes` ([<] :< PairC (ShapeCode re1) (ShapeCode re2)))
      encodes = replace
                  {p=(`Encodes` ([<] :< PairC (ShapeCode re1) (ShapeCode re2)))}
                  (cong (:< PairMark) appendNilLeftNeutral)
                  (APair Lin encodes1 encodes2)
  in rewrite p.routineEq in rewrite routineEquality in (ev1 ++ ev2 ++ [< PairMark]
        ** rewrite eq2 in (rewrite eq1 in (cong (:< PairMark) (sym $ appendAssociative), encodes)))

thompsonRoutinePrf (Group re) (Start (Right z) initprf acc) _ = absurd (rightCantBeElemOfLeft _ _ initprf)
thompsonRoutinePrf (Group re) (Start (Left z) initprf (Accept (Left z) pos)) _ = absurd pos
thompsonRoutinePrf (Group re) (Start (Left z) initprf (Step (Left z) c t prf acc)) (mc,vm) =
  let q := extractBasedOnFstFromRep (thompson (Group re)).nfa.start ((the Routine) [Record]) initprf
      (w ** ev) := evidenceForGroup re {mc,ev = vm.evidence}
                      (Step {nfa = (thompson (Group re)).nfa} (Left z) c t prf acc)
                      (MkVMState True vm.memory vm.evidence) Refl
  in ([< GroupMark w] ** rewrite q in (rewrite ev in (Refl, AGroup [<] w)))

thompsonRoutinePrf (Alt re1 re2) acc mcvm with (altEvidencePrf re1 re2 acc)
  thompsonRoutinePrf (Alt re1 re2) acc mcvm | (Left (MkAltEvidencePrfLeftData word1 acc1 routineEq)) =
    let (ev ** (eq, encodesPrev)) := thompsonRoutinePrf re1 acc1 mcvm
        encodes : (ev ++ [< LeftBranchMark]) `Encodes` ([<] :< EitherC (ShapeCode re1) (ShapeCode re2))
        encodes = replace {p=(`Encodes` ([<] :< EitherC (ShapeCode re1) (ShapeCode re2)))}
                      (cong (:< LeftBranchMark) appendNilLeftNeutral)
                      (ALeft Lin encodesPrev (ShapeCode re2))
    in rewrite routineEq in (ev ++ [< LeftBranchMark] **
                            (trans  (altLeftEqPrf _ _)
                                    (cong (:< LeftBranchMark) eq),
                            encodes))

  thompsonRoutinePrf (Alt re1 re2) acc mcvm | (Right (MkAltEvidencePrfRightData word2 acc2 routineEq)) =
    let (ev ** (eq, encodesPrev)) := thompsonRoutinePrf re2 acc2 mcvm
        encodes : (ev ++ [< RightBranchMark]) `Encodes` ([<] :< EitherC (ShapeCode re1) (ShapeCode re2))
        encodes = replace {p=(`Encodes` ([<] :< EitherC (ShapeCode re1) (ShapeCode re2)))}
                      (cong (:< RightBranchMark) appendNilLeftNeutral)
                      (ARight Lin encodesPrev (ShapeCode re1))
    in rewrite routineEq in (ev ++ [< RightBranchMark] **
                            (trans  (altRightEqPrf _ _)
                                    (cong (:< RightBranchMark) eq),
                            encodes))
public export
thompsonPrf : (re : CoreRE)
            -> (acc: Accepting (thompson re).nfa word)
            -> (extractEvidence {nfa = (thompson re).nfa, prog = (thompson re).prog} acc `Encodes` [< ShapeCode re])

thompsonPrf re acc =
  let rprf := extractRoutinePrf (thompson re).nfa (thompson re).prog acc
      (ev ** (concat, encodes)) := thompsonRoutinePrf re acc (Nothing, initVM)
      prf : (ev = extractEvidence {nfa = (thompson re).nfa, prog = (thompson re).prog} acc)
      prf = trans (sym $ appendNilLeftNeutral {x = ev}) (trans (sym concat) rprf)
  in replace {p=(\e => e `Encodes` [< ShapeCode re])} prf encodes
