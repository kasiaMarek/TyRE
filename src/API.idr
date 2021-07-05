module API

import Core
import Evidence
import NFA
import NFA.Thompson
import Codes
import Verification.AcceptingPath
import Verification
import Verification.Thompson
import StringRE

%default total

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
showREResult : {auto showChar : Show Char}
            -> {auto showString : Show String}
            -> {auto showPair : {0 a,b : Type} -> (Show a, Show b) => Show (a,b)}
            -> (re : CoreRE) -> Show (Shape re)
showREResult (Pred f) = showChar
showREResult (Concat x y) =
  let _ := showREResult x
      _ := showREResult y
  in showPair
showREResult (Group x) = showString

public export
showREResultCond : {auto showMaybe : {0 a : Type} -> (Show a) => Show (Maybe a)}
            -> (mre: Maybe RE) -> Show (case mre of {Just re => Maybe (Shape (compile re)); Nothing => Maybe ()})
showREResultCond Nothing = showMaybe
showREResultCond (Just re) =
  let _ := showREResult (compile re)
  in showMaybe

public export
run : (re: CoreRE) -> String -> Maybe (Shape re)
run re str = runWord re (unpack str)

public export
runCond : (mre: Maybe RE) -> String -> (case mre of {Just re => Maybe (Shape (compile re)); Nothing => Maybe ()})
runCond (Just re) str = runWord (compile re) (unpack str)
runCond Nothing str = Nothing
