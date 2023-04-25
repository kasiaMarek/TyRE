import Data.Regex
import Data.Either

typ : Nat -> Type
typ 0 = ()
typ (S k) = Either () (typ k)

rightRE : (n : Nat) -> TyRE (typ n)
rightRE 0 = match 'a'
rightRE (S k) = (match 'a' <|> rightRE k)

toNat : {n : Nat} -> typ n -> Nat
toNat {n = 0} () = 1
toNat {n = (S j)} (Left x) = j + 1
toNat {n = (S j)} (Right x) = toNat x

main : IO ()
main =  do  str <- getLine
            if all isDigit (unpack str)
              then
                let n : Nat
                    n = (cast str)
                in case parse (rightRE n) "a" of
                    Just res => putStrLn $ show $ toNat $ res
                    Nothing => putStrLn "Error"
              else putStrLn "Input should be two numbers"
