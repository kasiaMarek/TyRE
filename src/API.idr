module API

import public Core
import Evidence
import NFA
import NFA.Thompson
import Verification.AcceptingPath
import Verification
import Verification.Thompson
import StringRE
import CoreTyRE

%default total

public export
runAutomatonSM : SM -> Word -> Maybe Evidence
runAutomatonSM sm word = runAutomaton {N = sm.nfa, P = sm.prog} word

public export
match : {re : CoreRE} -> (sm : SM) -> {auto prf : thompson re = sm} -> Word -> Maybe (Shape re)
match {re} sm {prf} str with (runAutomatonSM sm str) proof p
  match {re} sm {prf} str | Nothing = Nothing
  match {re} sm {prf} str | Just ev =
    let 0 acc = extractEvidenceEquality (thompson re).nfa (thompson re).prog str ev (rewrite prf in p)
        0 encodes = thompsonPrf re (fst acc)
    in Just $ extract ev (rewrite (sym $ snd acc) in encodes)

public export
runWord : (re: CoreRE) -> List Char -> Maybe (Shape re)
runWord re str = match (thompson re) str

public export
run : (re: CoreRE) -> String -> Maybe (Shape re)
run re str = runWord re (unpack str)

public export
parse : CoreTyRE a -> String -> Maybe a
parse tyre str = map (extract tyre) $ run (compile tyre) str
