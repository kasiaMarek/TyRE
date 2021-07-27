import API
import Core
import NFA.Thompson
import Evidence
import Data.Maybe

A : CoreRE
A = Pred (\c =>  c == 'a')

createRE : Nat -> CoreRE
createRE 0 = (A `Alt` Empty)
createRE (S k) = (A `Alt` Empty) `Concat` (createRE k)

createString : Nat -> List Char
createString 0 = ['a']
createString (S k) = 'a'::(createString k)

printResult : (n: Nat) -> (k: Nat) -> Maybe (Shape $ createRE n)
printResult n k = runWord (createRE n) (createString k)

main : IO ()
main =  do  strn <- getLine
            strk <- getLine
            if (all isDigit (unpack strn)) && (all isDigit (unpack strk))
              then
                let n : Nat
                    n = (cast strn)
                    k : Nat
                    k = (cast strk)
                in case printResult n k of
                    Just res => putStrLn (showAux res)
                    Nothing => putStrLn "Error"
              else putStrLn "Input is not a number"
