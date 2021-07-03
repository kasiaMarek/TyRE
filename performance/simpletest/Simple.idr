import API
import Core
import Codes
import NFA.Thompson
import Evidence
import Data.Maybe

A : CoreRE
A = Pred (\c =>  c == 'a')

createRE : Nat -> CoreRE
createRE 0 = A
createRE (S k) = A `Concat` (createRE k)

createString : Nat -> List Char
createString 0 = ['a']
createString (S k) = 'a'::(createString k)

resToStr  : {auto showChar : Show Char }
          -> {auto showEither : ({a,b : Type} -> (Show a, Show b) => Show (a, b))}
          -> (n: Nat) -> Show (Shape $ createRE n)
resToStr 0 = showChar
resToStr (S k) =
  let _ := resToStr k
  in showEither

printResult : (n: Nat) -> Maybe (Shape $ createRE n)
printResult n = runWord (createRE n) (createString n)

main : IO ()
main =  do  str <- getLine
            if all isDigit (unpack str)
              then
                let n : Nat
                    n = (cast str)
                    _ := resToStr n
                in case printResult n of
                    Just res => putStrLn (show res ++ "\n")
                    Nothing => putStrLn "Error\n"
              else putStrLn "Input is not a number\n"
