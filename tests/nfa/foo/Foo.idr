import Data.Vect

import TyRE.NFA
import TyRE.Evidence

--Language accepting "foo"
data CState = Empty | F | FO

Eq CState where
  Empty == Empty  = True
  F     == F      = True
  FO    == FO     = True
  _     == _      = False

cNext : CState -> Char -> List (Maybe CState)
cNext Empty c = if (c == 'f') then [(Just F)]   else []
cNext F     c = if (c == 'o') then [(Just FO)]  else []
cNext FO    c = if (c == 'o') then [Nothing] else []

c : NA
c = MkNFA CState [(Just Empty)] cNext

cAcceptExamples : List Word
cAcceptExamples = map unpack ["foo"]

cRejectsExamples : List Word
cRejectsExamples = map unpack ["fo", "f", "", "fooo"]

main : IO ()
main = do putStrLn $ show $ map (runNFA c) cAcceptExamples
          putStrLn $ show $ map (runNFA c) cRejectsExamples
