module Data.Regex

import public TyRE.StringRE
import public TyRE.DisjointMatches
import TyRE.Parser

%default total

export
parse : TyRE a -> String -> Maybe a
parse tyre str = parseFull tyre (fastUnpack str)

export
match : TyRE a -> String -> Bool
match tyre str = isJust $ parse (ignore tyre) str

export
parsePrefix : (tyre : TyRE a) -> String -> (greedy : Bool) -> (Maybe a, String)
parsePrefix tyre cs greedy =
  bimap id fastPack (parsePrefix tyre (fastUnpack cs) greedy)

export
partial
getToken : (greedy : Bool) -> TyRE a -> Stream Char -> (Maybe a, Stream Char)
getToken greedy tyre stm = getToken tyre stm greedy

export
partial -- consuming makes this function terminating, however we do not prove this
asDisjointMatches : (tyre : TyRE a) -> {auto 0 consuming : IsConsuming tyre}
                  -> String -> (greedy : Bool) -> DisjointMatches a
asDisjointMatches tyre str greedy
  = asDisjointMatches tyre (fastUnpack str) greedy

export
partial
substitute : (tyre: TyRE a) -> {auto 0 consuming : IsConsuming tyre}
          -> (a -> String) -> String -> String
substitute tyre f str = toString f (asDisjointMatches tyre str True)