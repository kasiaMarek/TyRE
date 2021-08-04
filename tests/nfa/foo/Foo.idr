import NFA
import Data.Vect
import Evidence

runNFA : NA -> Word -> Bool
runNFA na word = run {N = na} word na.start

--Language accepting "foo"
data CState = Empty | F | FO | FOO

Eq CState where
  Empty == Empty  = True
  F     == F      = True
  FO    == FO     = True
  FOO   == FOO    = True
  _     == _      = False

cAccepting : CState -> Bool
cAccepting FOO  = True
cAccepting _    = False

cNext : CState -> Char -> (xs: List CState ** Vect (length xs) Routine)
cNext Empty c = if (c == 'f') then ([F] ** [[]])    else ([] ** [])
cNext F     c = if (c == 'o') then ([FO] ** [[]])   else ([] ** [])
cNext FO    c = if (c == 'o') then ([FOO] ** [[EmitString]])   else ([] ** [])
cNext FOO   c = ([] ** [])

cNP : (n: NA ** Program n)
cNP =
  let start : (a: List CState ** Vect (length a) Routine)
      start = ([Empty] ** [[Record]])
  in (MkNFA CState cAccepting (fst start) (\s => \c => fst $ cNext s c)
        ** MkProgram (snd start) (\s => \c => snd $ cNext s c))

c : NA
c = fst cNP

cAcceptExamples : List Word
cAcceptExamples = map unpack ["foo"]

cRejectsExamples : List Word
cRejectsExamples = map unpack ["fo", "f", "", "fooo"]

main : IO ()
main = do putStrLn $ show $ map (runNFA c) cAcceptExamples
          putStrLn $ show $ map (runNFA c) cRejectsExamples
