module ConcatLastStep

import NFA
import Evidence
import Core
import NFA.Thompson

A : CoreRE
A = Pred (\c =>  c == 'a')

createRE : Nat -> CoreRE
createRE 0 = A
createRE (S k) = A `Concat` (createRE k)

state : (n : Nat) -> ((thompson (createRE n)).nfa.State)
state 0 = StartState
state (S k) = CTh2 (state k)

lastStep : (n : Nat) -> Maybe Evidence
lastStep n = 
    let sm : SM 
        sm = thompson (createRE n)
    in runFrom {N = sm.nfa} {P = sm.prog} ['a'] [MkThread (state n) (MkVMState False Lin Lin)]

main : IO ()
main =  do  str <- getLine
            if all isDigit (unpack str)
              then
                let n : Nat
                    n = (cast str)
                in case lastStep n of
                    Just _ => putStrLn "Fine\n"
                    Nothing => putStrLn "Error\n"
              else putStrLn "Input is not a number\n"