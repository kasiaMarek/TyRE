import Data.Maybe

import TyRE.Core
import TyRE.Parser

shape : Nat -> Type
shape 0 = Char
shape (S k) = (Char, shape k)

createRE : (n : Nat) -> TyRE (shape n)
createRE 0 = oneOfCharsList ['a']
createRE (S k) = (oneOfCharsList ['a']) <*> (createRE k)

createString : Nat -> List Char
createString 0 = ['a']
createString (S k) = 'a'::(createString k)

printResult : (n: Nat) -> Maybe (shape n)
printResult n = parseFull (createRE n) (createString n)

showAux : {n : Nat} -> (shape n) -> String
showAux {n = 0} c = show c
showAux {n = (S k)} (x, y) = "(" ++ show x ++ "," ++ showAux y ++ ")"

main : IO ()
main =  do  str <- getLine
            if all isDigit (unpack str)
              then
                let n : Nat
                    n = (cast str)
                in case printResult n of
                    Just res => putStrLn (showAux res)
                    Nothing => putStrLn "Error\n"
              else putStrLn "Input is not a number\n"
