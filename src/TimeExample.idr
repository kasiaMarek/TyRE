module TimeExample

import Core
import Evidence
import NFA
import NFA.Thompson
import Codes
import Verification.AcceptingPath
import Verification
import Verification.Routine.Thompson
import System.REPL

Exactly: Char -> CoreRE
Exactly x = Pred (\c =>  c == x)

Range: Char -> Char -> CoreRE
Range x y = Pred (\c =>  x <= c && c <= y)

Time: CoreRE
Time =
    (
        (
          ('0' `Range` '1')
          `Concat`
          ('0' `Range` '2')
        )
        `Concat`
        (Exactly ':')
    ) `Concat`
    (
        ('1' `Range` '5')
        `Concat`
        ('0' `Range` '9')
    )

runAutomaton' : SM -> String -> Maybe Evidence
runAutomaton' sm word = runAutomaton {N = sm.nfa, P = sm.prog} (unpack word)

run : (re: CoreRE) -> String -> Maybe (Shape re)
run re str with (runAutomaton' (thompson re) str) proof p
  run re str | Nothing = Nothing
  run re str | Just ev =
    let 0 acc = extractEvidenceEquality (thompson re).nfa (thompson re).prog (unpack str) ev p
        0 encodes = thompsonPrf re (fst acc)
    in Just $ extract ev (rewrite (sym $ snd acc) in encodes)

main : IO ()
main = repl "Enter a string: " (\x => (show (run Time x)) ++ "\n")
