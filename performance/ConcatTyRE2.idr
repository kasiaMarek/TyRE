import Data.Maybe

import TyRE.CoreRE
import TyRE.Parser2

A : CoreRE
A = CharPred (Pred (\c =>  c == 'a'))

createRE : Nat -> CoreRE
createRE 0 = A
createRE (S k) = A `Concat` (createRE k)

createString : Nat -> List Char
createString 0 = ['a']
createString (S k) = 'a'::(createString k)

printResult : (n: Nat) -> Maybe (Shape $ createRE n)
printResult n = parseFull (createRE n) (createString n)

main : IO ()
main =  do  str <- getLine
            if all isDigit (fastUnpack str)
              then
                let n : Nat
                    n = (cast str)
                in case printResult n of
                    Just res => putStrLn (showAux res)
                    Nothing => putStrLn "Error\n"
              else putStrLn "Input is not a number\n"
