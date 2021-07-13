module API

import public Core
import Evidence
import NFA
import NFA.Thompson
import Verification.AcceptingPath
import Verification
import Verification.Thompson
import CoreTyRE
import Data.Stream

public export
runAutomatonSM : SM -> Word -> Maybe Evidence
runAutomatonSM sm word = runAutomaton {N = sm.nfa, P = sm.prog} word

runAutomatonSMStream : SM -> Stream Char -> Maybe Evidence
runAutomatonSMStream sm stream = runAutomatonStream {N = sm.nfa, P = sm.prog} stream

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

public export
matchStream : {re : CoreRE} -> (sm : SM) -> {auto prf : thompson re = sm} -> Stream Char -> Maybe (Shape re)
matchStream {re} sm {prf} stm with (runAutomatonSMStream sm stm) proof p
  matchStream {re} sm {prf} stm | Nothing = Nothing
  matchStream {re} sm {prf} stm | Just ev =
    let 0 stmEq := eqForStream (thompson re).nfa (thompson re).prog stm
        0 acc := extractEvidenceEquality (thompson re).nfa (thompson re).prog (fst stmEq) ev (trans (snd stmEq) (rewrite prf in p))
        0 encodes := thompsonPrf re (fst acc)
    in Just $ extract ev (rewrite (sym $ snd acc) in encodes)

public export
getToken : (re: CoreRE) -> Stream Char -> Maybe (Shape re)
getToken re stm = matchStream (thompson re) stm
