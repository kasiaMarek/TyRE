module API

import public Core
import Evidence
import NFA
import Verification.AcceptingPath
import Verification
import Verification.Thompson
import TyRE
import Data.Stream
import Thompson

public export
runAutomatonSM : SM -> Word -> Maybe Evidence
runAutomatonSM sm word = runAutomaton word

runAutomatonSMStream : SM -> Stream Char -> Maybe Evidence
runAutomatonSMStream sm stream = runAutomatonStream stream

public export
match : {re : CoreRE} -> (sm : SM) -> {auto prf : thompson re = sm}
      -> Word -> Maybe (Shape re)
match {re} sm {prf} str with (runAutomatonSM sm str) proof p
  match {re} sm {prf} str | Nothing = Nothing
  match {re} sm {prf} str | Just ev =
    let 0 acc = extractEvidenceEquality (thompson re) str ev (rewrite prf in p)
        0 encodes = thompsonPrf re (fst acc)
    in Just $ extract ev (rewrite (sym $ snd acc) in encodes)

public export
runWord : (re: CoreRE) -> List Char -> Maybe (Shape re)
runWord re str = match (thompson re) str

public export
run : (re: CoreRE) -> String -> Maybe (Shape re)
run re str = runWord re (unpack str)

public export
parse : TyRE a -> String -> Maybe a
parse tyre str = map (extract tyre) $ run (compile tyre) str

public export
matchStream : {re : CoreRE} -> (sm : SM) -> {auto prf : thompson re = sm}
            -> Stream Char -> Maybe (Shape re)
matchStream {re} sm {prf} stm with (runAutomatonSMStream sm stm) proof p
  matchStream {re} sm {prf} stm | Nothing = Nothing
  matchStream {re} sm {prf} stm | Just ev =
    let 0 stmEq := eqForStream (thompson re) stm
        0 acc := extractEvidenceEquality (thompson re) (fst stmEq) ev (trans (snd stmEq) (rewrite prf in p))
        0 encodes := thompsonPrf re (fst acc)
    in Just $ extract ev (rewrite (sym $ snd acc) in encodes)

public export
getToken : (re: CoreRE) -> Stream Char -> Maybe (Shape re)
getToken re stm = matchStream (thompson re) stm
