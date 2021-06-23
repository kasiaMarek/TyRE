module Verification.Routine.Thompson

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
import Verification.Routine.Thompson.Group
import Data.Vect
import Extra.Reflects

thompsonRoutinePrf : (re : CoreRE)
                  -> (acc : Accepting (thompson re).nfa word)
                  -> (vm  : VMState)
                  -> (mc  : Maybe Char)
                  -> (ev  : Evidence ** (executeRoutineFrom (extractRoutine (thompson re).nfa (thompson re).prog acc) (mc, vm) = vm.evidence ++ ev, ev `Encodes` [< ShapeCode re]))

thompsonRoutinePrf (Pred f) (Start s (There prf) x) vm mc = absurd prf
thompsonRoutinePrf {word = []} (Pred f) (Start StartState Here (Accept StartState prf)) vm mc = absurd prf
thompsonRoutinePrf {word = c::_} (Pred f) (Start StartState Here (Step StartState c t prf acc)) vm mc with (f c)
  thompsonRoutinePrf {word = c::_} (Pred f) (Start StartState Here (Step StartState c t prf acc)) vm mc | False = absurd prf
  thompsonRoutinePrf {word = c::_} (Pred f) (Start StartState Here (Step StartState c t (There prf) acc)) vm mc | True = absurd prf
  thompsonRoutinePrf {word = c::c'::_} (Pred f) (Start StartState Here (Step StartState c AcceptState Here (Step AcceptState c' t prf acc))) vm mc | True = absurd prf
  thompsonRoutinePrf {word = [c]} (Pred f) (Start StartState Here (Step StartState c AcceptState Here (Accept AcceptState Refl))) vm mc | True = ([< CharMark c] ** (Refl, AChar [<] c))

thompsonRoutinePrf (Concat x y) acc vm mc = ?thompsonRoutinePrf_rhs_2

thompsonRoutinePrf (Group re) (Start (Right z) initprf acc) vm mc = absurd (rightCantBeElemOfLeft _ _ initprf)
thompsonRoutinePrf (Group re) (Start (Left z) initprf (Accept (Left z) pos)) vm mc = absurd pos
thompsonRoutinePrf (Group re) (Start (Left z) initprf (Step (Left z) c t prf acc)) vm mc =
  let q := extractBasedOnFstFromRep (thompson (Group re)).nfa.start ((the Routine) [Record]) (Left z) initprf
      (w ** ev) := evidenceForGroup re {mc,ev = vm.evidence} (Step {nfa = (thompson (Group re)).nfa} (Left z) c t prf acc) (MkVMState True vm.memory vm.evidence) Refl
  in ([< GroupMark w] ** rewrite q in (rewrite ev in (Refl, AGroup [<] w)))

thompsonPrf : (re : CoreRE)
            -> (acc: Accepting (thompson re).nfa word)
            -> (extractEvidence {nfa = (thompson re).nfa, prog = (thompson re).prog} acc `Encodes` [< ShapeCode re])

thompsonPrf re acc =
  let rprf := extractRoutinePrf (thompson re).nfa (thompson re).prog acc
      (ev ** (concat, encodes)) := thompsonRoutinePrf re acc initVM Nothing
      prf : (ev = extractEvidence {nfa = (thompson re).nfa, prog = (thompson re).prog} acc)
      prf = trans (sym $ appendNilLeftNeutral {x = ev}) (trans (sym concat) rprf)
  in replace {p=(\e => e `Encodes` [< ShapeCode re])} prf encodes
