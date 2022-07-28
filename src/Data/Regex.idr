module Data.Regex

import public StringRE
import API

export
getToken : TyRE a -> Stream Char -> (Maybe a, Stream Char)
getToken tyre stm = 
  let (pres, stmTail) := getTokenCore (compile tyre) stm 
  in (map (extract tyre) pres, stmTail)

export
parse : TyRE a -> String -> Maybe a
parse tyre str = map (extract tyre) $ run (compile tyre) str

export
match : TyRE a -> String -> Bool
match tyre str = isJust $ parse (ignore tyre) str