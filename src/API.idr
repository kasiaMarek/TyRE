module API

import Core
import Evidence
import NFA
import NFA.Thompson
import Codes
import Verification.AcceptingPath
import Verification
import Verification.Routine.Thompson

runAutomatonSM : SM -> String -> Maybe Evidence
runAutomatonSM sm word = runAutomaton {N = sm.nfa, P = sm.prog} (unpack word)

public export
match : {re : CoreRE} -> (sm : SM) -> {auto prf : thompson re = sm} -> String -> Maybe (Shape re)
match {re} sm {prf} str with (runAutomatonSM sm str) proof p
  match {re} sm {prf} str | Nothing = Nothing
  match {re} sm {prf} str | Just ev =
    let 0 acc = extractEvidenceEquality (thompson re).nfa (thompson re).prog (unpack str) ev (rewrite prf in p)
        0 encodes = thompsonPrf re (fst acc)
    in Just $ extract ev (rewrite (sym $ snd acc) in encodes)

public export
run : (re: CoreRE) -> String -> Maybe (Shape re)
run re str = match (thompson re) str
