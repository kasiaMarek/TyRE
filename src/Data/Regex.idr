module Data.Regex

import public TyRE.StringRE
import public TyRE.DisjointMatches
import TyRE.API

%default total

export
parse : TyRE a -> String -> Maybe a
parse tyre str = map (extract tyre) $ run (compile tyre) str

export
match : TyRE a -> String -> Bool
match tyre str = isJust $ parse (ignore tyre) str

export
partial
getToken : TyRE a -> Stream Char -> (greedy : Bool) -> Maybe (a, Stream Char)
getToken tyre stm greedy = 
  map (\case (pres, stmTail) => (extract tyre pres, stmTail)) 
      (getTokenCore (compile tyre) stm greedy)

export
partial --we should be able to prove totality thanks to `consuming`
asDisjointMatches : (tyre : TyRE a) -> {auto 0 consuming : IsConsuming tyre}
                  -> String -> (greedy : Bool) -> DisjointMatches a
asDisjointMatches tyre str greedy {consuming}
  = map (extract tyre) 
        (asDisjoinMatchesCore (compile tyre) str greedy
                              {consuming = consumingImpl consuming})

export
partial
substitute : (tyre: TyRE a) -> {auto 0 consuming : IsConsuming tyre}
          -> (a -> String) -> String -> String
substitute tyre f str = toString f (asDisjointMatches tyre str True)

export
parsePrefix : (tyre : TyRE a) -> String -> Maybe (a, String)
parsePrefix tyre cs = map (bimap (extract tyre) id)
                          (parsePrefix (compile tyre) cs)