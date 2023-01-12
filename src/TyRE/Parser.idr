module TyRE.Parser

import Data.Maybe

import TyRE.Core
import TyRE.Parser.SM
import TyRE.Parser.SMConstruction
import TyRE.DisjointMatches

%default total

export
parseFull : (r : TyRE a) -> List Char -> Maybe a
parseFull re cs =
  let _ := compile re
  in runFromInit (runTillStrEnd cs)

export
parsePrefix : (r : TyRE a) -> List Char -> (greedy : Bool)
            -> (Maybe a, List Char)
parsePrefix re cs False =
  let _ = compile re
  in runFromInit (runTillFirstAccept cs)
parsePrefix re cs True =
  let _ = compile re
  in runFromInit (runTillLastAccept cs Nothing)

export
partial --we should be able to prove totality thanks to `consuming`
asDisjointMatches : (re : TyRE a) -> {auto 0 consuming : IsConsuming re}
                  -> List Char -> (greedy : Bool)
                  -> DisjointMatches a
asDisjointMatches re cs greedy =
  let _ = compile re
      parseFunction : List Char -> (Maybe a, List Char)
      parseFunction cs =
        if greedy
        then runFromInit (runTillLastAccept cs Nothing)
        else runFromInit (runTillFirstAccept cs)
      matchesRec : List Char -> DisjointMatchesSnoc a
                -> DisjointMatchesSnoc a 
      matchesRec [] dm = dm
      matchesRec (x :: xs) dm with (parseFunction (x :: xs))
        matchesRec (x :: xs) dm | (Nothing, _) = matchesRec xs (dm :< x)
        matchesRec (x :: xs) dm | ((Just tree), tail) =
          matchesRec tail (dm :+: tree)
  in cast (matchesRec cs (Prefix [<]))

export
partial
getToken : (r : TyRE a) -> Stream Char -> (greedy : Bool)
        -> (Maybe a, Stream Char)
getToken re cs False =
  let _ = compile re
  in runFromInit (runTillFirstAccept cs)
getToken re cs True =
  let _ = compile re
  in runFromInit (runTillLastAccept cs Nothing)
