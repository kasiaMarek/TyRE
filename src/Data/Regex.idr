module Data.Regex

import public TyRE.StringRE
import public TyRE.DisjointMatches
import TyRE.API

export
getToken : TyRE a -> Stream Char -> (greedy : Bool) -> Maybe (a, Stream Char)
getToken tyre stm greedy = 
  map (\case (pres, stmTail) => (extract tyre pres, stmTail)) 
      (getTokenCore (compile tyre) stm greedy)

export
parse : TyRE a -> String -> Maybe a
parse tyre str = map (extract tyre) $ run (compile tyre) str

export
match : TyRE a -> String -> Bool
match tyre str = isJust $ parse (ignore tyre) str

export
asDisjointMatches : TyRE a -> String -> (greedy : Bool) -> DisjointMatches a
asDisjointMatches tyre str greedy
  = map (extract tyre) 
        (asDisjoinMatchesCore (compile tyre) str greedy)

export
substitute : TyRE a -> (a -> String) -> String -> String
substitute tyre f str = toString f (asDisjointMatches tyre str True)