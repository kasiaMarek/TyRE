module NFA.Examples

import NFA

-- parameters {auto N : NA}

--TODO: probably should be on Set of States not list
runNFA : NA -> Word -> Bool
runNFA na word =
  let runNFArec: Word -> List (na .State) -> Bool
      runNFArec [] [] = False
      runNFArec [] (s :: ss) = if (na.accepting s) then True else runNFArec [] ss
      runNFArec (c :: cs) ys = runNFArec cs (ys >>= (\s => na.next s c))
  in runNFArec word na.start

--a. Automaton for language accepting words with even numbers.
-- I assume words that cointain at least one even number
data AState = FinishAcc | Start | NumStateAcc | NumStateRej

Eq AState where
  FinishAcc     == FinishAcc    = True
  Start         == Start        = True
  NumStateAcc   == NumStateAcc  = True
  NumStateRej   == NumStateRej  = True
  _             == _            = False

aAccepting : AState -> Bool
aAccepting FinishAcc    = True
aAccepting Start        = False
aAccepting NumStateAcc  = True
aAccepting NumStateRej  = False

aNext : AState -> Char -> List AState
aNext NumStateAcc   c = if (isDigit c) then if (ord c `mod` 2 == 1) then [NumStateRej] else [NumStateAcc] else [FinishAcc]
aNext FinishAcc     _ = [FinishAcc]
aNext _             c = if (isDigit c) then if (ord c `mod` 2 == 1) then [NumStateRej] else [NumStateAcc] else [Start]

a : NA
a = MkNFA AState aAccepting [Start] aNext

aAcceptExamples : List Word
aAcceptExamples = map unpack ["46ghjn56jij", "46ghjn57lljij", "uwb77hui2hu9"]

aRejectsExamples : List Word
aRejectsExamples = map unpack ["ghjn87jij", "463ghjn57lljij", "uwb77hui29221hu9"]

--Empty Languge
b : NA
b = MkNFA Nat (\x => False) [] (\s => \c => [])

bRejectsExamples : List Word
bRejectsExamples = map unpack ["bhcjbawc", "xua", "cewyubc"]

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

cNext : CState -> Char -> List CState
cNext Empty c = if (c == 'f') then [F]     else []
cNext F     c = if (c == 'o') then [FO]    else []
cNext FO    c = if (c == 'o') then [FOO]   else []
cNext FOO   c = []

c : NA
c = MkNFA CState cAccepting [Empty] cNext

cAcceptExamples : List Word
cAcceptExamples = map unpack ["foo"]

cRejectsExamples : List Word
cRejectsExamples = map unpack ["fo", "f", "", "fooo"]
