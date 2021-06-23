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

thompsonRoutinePrf : (re : CoreRE)
                  -> (acc : Accepting (thompson re).nfa word)
                  -> (vm  : VMState)
                  -> (mc  : Maybe Char)
                  -> (ev  : Evidence ** (executeRoutineFrom (extractRoutine (thompson re).nfa (thompson re).prog acc) (mc, vm) = vm.evidence ++ ev, ev `Encodes` [< ShapeCode re]))



thompsonPrf : (re : CoreRE)
            -> (acc: Accepting (thompson re).nfa word)
            -> (extractEvidence {nfa = (thompson re).nfa, prog = (thompson re).prog} acc `Encodes` [< ShapeCode re])

thompsonPrf re acc =
  let rprf := extractRoutinePrf (thompson re).nfa (thompson re).prog acc
      (ev ** (concat, encodes)) := thompsonRoutinePrf re acc initVM Nothing
      prf : (ev = extractEvidence {nfa = (thompson re).nfa, prog = (thompson re).prog} acc)
      prf = trans (sym $ appendNilLeftNeutral {x = ev}) (trans (sym concat) rprf)
  in replace {p=(\e => e `Encodes` [< ShapeCode re])} prf encodes
