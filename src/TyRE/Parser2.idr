module TyRE.Parser2

import Data.Maybe

import TyRE.Codes
import TyRE.CoreRE
import TyRE.Parser2.SM
import TyRE.Parser2.SMConstruction
import TyRE.DisjointMatches

%default total

export
parseFull : (r : CoreRE) -> List Char -> Maybe (Shape r)
parseFull re cs =
  let _ := compile re
  in runFromInit (runTillStrEnd cs)

export
parsePrefix : (r : CoreRE) -> List Char -> (greedy : Bool)
            -> (Maybe (Shape r), List Char)
parsePrefix re cs False =
  let _ = compile re
  in runFromInit (runTillFirstAccept cs)
parsePrefix re cs True =
  let _ = compile re
  in runFromInit (runTillLastAccept cs Nothing)

export
partial --we should be able to prove totality thanks to `consuming`
asDisjointMatches : (re : CoreRE) -> {auto 0 consuming : IsConsuming re}
                  -> List Char -> (greedy : Bool)
                  -> DisjointMatches (Shape re)
asDisjointMatches re cs greedy =
  let _ = compile re
      parseFunction : List Char -> (Maybe (Shape re), List Char)
      parseFunction cs =
        if greedy
        then runFromInit (runTillLastAccept cs Nothing)
        else runFromInit (runTillFirstAccept cs)
      matchesRec : List Char -> DisjointMatchesSnoc (Shape re)
                -> DisjointMatchesSnoc (Shape re) 
      matchesRec [] dm = dm
      matchesRec (x :: xs) dm with (parseFunction (x :: xs))
        matchesRec (x :: xs) dm | (Nothing, _) = matchesRec xs (dm :< x)
        matchesRec (x :: xs) dm | ((Just tree), tail) =
          matchesRec tail (dm :+: tree)
  in cast (matchesRec cs (Prefix [<]))

export
partial
getToken : (r : CoreRE) -> Stream Char -> (greedy : Bool)
        -> (Maybe (Shape r), Stream Char)
getToken re cs False =
  let _ = compile re
  in runFromInit (runTillFirstAccept cs)
getToken re cs True =
  let _ = compile re
  in runFromInit (runTillLastAccept cs Nothing)
