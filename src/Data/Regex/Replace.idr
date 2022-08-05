module Data.Regex.Replace

import public Data.Regex

export
replace : TyRE a -> (a -> String) -> String -> String
replace tyre f str = toString f (asDisjoinMatches tyre str)

export
sed : List (String -> String) -> String -> String
sed [] str = str
sed (t :: ts) str = sed ts (t str)
