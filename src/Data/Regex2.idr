module Data.Regex2

import public TyRE.StringRE
import public TyRE.DisjointMatches
import TyRE.Parser2

%default total

export
parse : TyRE a -> String -> Maybe a
parse tyre str = map (extract tyre) $ parseFull (compile tyre) (unpack str)

export
match : TyRE a -> String -> Bool
match tyre str = isJust $ parse (ignore tyre) str

export
parsePrefix : (tyre : TyRE a) -> String -> (greedy : Bool) -> (Maybe a, String)
parsePrefix tyre cs greedy =
  bimap (map (extract tyre)) pack
        (parsePrefix (compile tyre) (unpack cs) greedy)

export
partial
getToken : TyRE a -> Stream Char -> (greedy : Bool) -> (Maybe a, Stream Char)
getToken tyre stm greedy = 
  bimap (map (extract tyre)) id (getToken (compile tyre) stm greedy)

export
partial -- consuming makes this function terminating, however we do not prove this
asDisjointMatches : (tyre : TyRE a) -> {auto 0 consuming : IsConsuming tyre}
                  -> String -> (greedy : Bool) -> DisjointMatches a
asDisjointMatches tyre str greedy {consuming}
  = map (extract tyre) $
        asDisjointMatches (compile tyre) (unpack str) greedy
                          {consuming = consumingImpl consuming}

export
partial
substitute : (tyre: TyRE a) -> {auto 0 consuming : IsConsuming tyre}
          -> (a -> String) -> String -> String
substitute tyre f str = toString f (asDisjointMatches tyre str True)