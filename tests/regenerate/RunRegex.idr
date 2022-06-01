import API
import StringRE
import CommonRegexes
import CommonRegexes.DateAndTime

import Data.List

regexes : List (String, (a : Type ** (TyRE a, a -> String)))
regexes = 
    [
        ("email",   (_ **   (email, show)   ))
    ,   ("url",     (_ **   (url,   show)   ))
    ,   ("time",    (_ **   (time,  show)   ))
    ,   ("date",    (_ **   (date,  show)   ))
    ,   ("iso",     (_ **   (iso,   show)   ))
    ]

main : IO ()
main =  do  re <- getLine
            case (find (\case (s, _) => re == s) regexes) of
                Nothing => putStrLn "input not valid"
                (Just (_, (_ ** (tyre, toStr)))) =>
                    do  str <- getLine
                        case (parse tyre str) of
                            Nothing => putStrLn "--NO MATCH--"
                            Just res => putStrLn $ toStr res
