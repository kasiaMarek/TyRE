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

runAutomatonSM : SM -> Word -> Maybe Evidence
runAutomatonSM sm word = runAutomaton word

runAutomatonSMStream : SM -> Stream Char -> (Maybe Evidence, Stream Char)
runAutomatonSMStream sm stream = runAutomatonStream stream

match : {re : CoreRE} -> (sm : SM) -> {auto prf : thompson re = sm}
      -> Word -> Maybe (Shape re)
match {re} sm {prf} str with (runAutomatonSM sm str) proof p
  match {re} sm {prf} str | Nothing = Nothing
  match {re} sm {prf} str | Just ev =
    let 0 acc = extractEvidenceEquality (thompson re) str ev (rewrite prf in p)
        0 encodes = thompsonPrf re (fst acc)
    in Just $ extract ev (rewrite (sym $ snd acc) in encodes)

runWord : (re : CoreRE) -> List Char -> Maybe (Shape re)
runWord re str = match (thompson re) str

export
run : (re : CoreRE) -> String -> Maybe (Shape re)
run re str = runWord re (unpack str)

export
parse : TyRE a -> String -> Maybe a
parse tyre str = map (extract tyre) $ run (compile tyre) str

matchStream : {re : CoreRE} -> (sm : SM) -> {auto prf : thompson re = sm}
            -> Stream Char -> (Maybe (Shape re), Stream Char)
matchStream {re} sm {prf} stm with (runAutomatonSMStream sm stm) proof p
  matchStream {re} sm {prf} stm | (Nothing, stmTail) = (Nothing, stmTail)
  matchStream {re} sm {prf} stm | (Just ev, stmTail) =
    let 0 stmEq := eqForStream (thompson re) stm
        0 acc := extractEvidenceEquality (thompson re) (fst stmEq) ev (trans (snd stmEq) (rewrite prf in (cong fst p)))
        0 encodes := thompsonPrf re (fst acc)
    in (Just $ extract ev (rewrite (sym $ snd acc) in encodes), stmTail)

export
getTokenCore : (re : CoreRE) -> Stream Char -> (Maybe (Shape re), Stream Char)
getTokenCore re stm = matchStream (thompson re) stm

export
getToken : TyRE a -> Stream Char -> (Maybe a, Stream Char)
getToken tyre stm = 
  let (pres, stmTail) := getTokenCore (compile tyre) stm 
  in (map (extract tyre) pres, stmTail)
