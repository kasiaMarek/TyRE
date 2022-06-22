import NFA
import Data.Vect
import Evidence

--a. Automaton for language accepting words with even numbers.
-- I assume words that cointain at least one even number
data AState = FinishAcc | Start | NumStateAcc | NumStateRej

Eq AState where
  FinishAcc     == FinishAcc    = True
  Start         == Start        = True
  NumStateAcc   == NumStateAcc  = True
  NumStateRej   == NumStateRej  = True
  _             == _            = False

aNext : AState -> Char -> List (Maybe AState)
aNext NumStateAcc   c = if (isDigit c)
                        then if (ord c `mod` 2 == 1) then [Just NumStateRej] else [Just NumStateAcc, Nothing]
                        else [Just FinishAcc, Nothing]

aNext FinishAcc     _ = [Just FinishAcc, Nothing]
aNext _             c = if (isDigit c)
                        then if (ord c `mod` 2 == 1) then [Just NumStateRej] else [Just NumStateAcc, Nothing]
                        else [Just Start]

a : NA
a = MkNFA AState [Just Start] aNext

aAcceptExamples : List Word
aAcceptExamples = map unpack ["46ghjn56jij", "46ghjn57lljij", "uwb77hui2hu9"]

aRejectsExamples : List Word
aRejectsExamples = map unpack ["ghjn87jij", "463ghjn57lljij", "uwb77hui29221hu9"]

main : IO ()
main = do putStrLn $ show $ map (runNFA a) aAcceptExamples
          putStrLn $ show $ map (runNFA a) aRejectsExamples
