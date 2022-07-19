import Data.Regex
import Data.Nat

altRE : Nat -> TyRE ()
altRE 0 = match 'a'
altRE (S k) = ignore (match 'a' <|> altRE k)

main : IO ()
main =  do  isGroup <- getLine
            str <- getLine
            if all isDigit (unpack str)
              then
                let n : Nat
                    n = (cast str)
                    n' := power 2 n
                    re := if isGroup == "group" then (ignore (group (altRE n'))) else (altRE n')
                in case parse re "a" of
                    Just res => putStrLn $ "Matches"
                    Nothing => putStrLn "Error"
              else putStrLn "Input should be two numbers"
