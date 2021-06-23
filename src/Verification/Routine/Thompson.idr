module Verification.Routine.Thompson

thompsonRoutinePrf : (re : CoreRE)
                  -> (acc : Accepting (thompson re).nfa word)
                  -> (vm  : VMState)
                  -> (mc  : Maybe Char)
                  -> (ev  : Evidence ** (executeRoutineFrom (fst $ extractRoutine (thompson re).nfa (thompson re).prog acc) (mc, vm) = vm.evidence ++ ev, ev `Encodes` [< ShapeCode re]))





thompsonPrf : (re : CoreRE)
            -> (acc: Accepting (thompson re).nfa word)
            -> (extractEvidence {nfa = (thompson re).nfa, prog = (thompson re).prog} acc `Encodes` [< ShapeCode re])

thompsonPrf re acc =
  let r : (routine: ExtendedRoutine ** executeRoutine routine = extractEvidence {nfa = (thompson re).nfa, prog = (thompson re).prog} acc)
      r = extractRoutine (thompson re).nfa (thompson re).prog acc
      (ev ** (concat, encodes)) := thompsonRoutinePrf re acc initVM Nothing
      prf : (ev = extractEvidence {nfa = (thompson re).nfa, prog = (thompson re).prog} acc)
      prf = trans (sym $ appendNilLeftNeutral {x = ev}) (trans (sym concat) (snd r))
  in replace {p=(\e => e `Encodes` [< ShapeCode re])} prf encodes
