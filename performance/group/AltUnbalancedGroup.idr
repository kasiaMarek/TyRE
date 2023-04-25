import Data.Regex
import Data.Either

typ : Nat -> Type
typ 0 = ()
typ (S k) = Either () (typ k)

rightRE : (n : Nat) -> TyRE (typ n)
rightRE 0 = match 'a'
rightRE (S k) = (match 'a' <|> rightRE k)

main : IO ()
main =  do  str <- getLine
            if all isDigit (unpack str)
              then
                let n : Nat
                    n = (cast str)
                in case parse (ignore (rightRE n)) "a" of
                    Just res => putStrLn $ show $ res
                    Nothing => putStrLn "Error"
              else putStrLn "Input should be two numbers"
