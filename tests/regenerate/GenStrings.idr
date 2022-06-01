import StringRE
import CommonRegexes
import CommonRegexes.DateAndTime

import Data.List

regexes : List (String, Lazy String)
regexes = 
    [
        ("email", translate email emailZipper)
    ,   ("url", translate url urlZipper)
    ,   ("time", translate time timeZipper)
    ,   ("date", translate date dateZipper)
    ,   ("iso", translate iso isoZipper)
    ]

main : IO ()
main =  do  str <- getLine
            case (find (\case (s, _) => str == s) regexes) of
                Nothing => putStrLn "input not valid"
                (Just (_, re)) => putStrLn re
