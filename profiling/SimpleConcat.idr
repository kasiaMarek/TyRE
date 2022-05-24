module SimpleConcat

import API
import Profiling.NFA
import NFA
import NFA.Thompson
import Profiling

length : Nat
length = 5

stateType : (n : Nat) -> {auto p : n = S k} -> Type
stateType (S 0) = PState
stateType (S (S k)) = CState PState (stateType (S k))

createTyRE : (n : Nat) -> {auto p : n = S k} -> CoreRE
createTyRE (S 0) = Pred (\c =>  c == 'a')
createTyRE (S (S k)) = Pred (\c =>  c == 'a') `Concat` createTyRE (S k)

string : (n : Nat) -> {auto p : n = S k} -> List Char
string (S 0) = ['a']
string (S (S k)) = 'a' :: (string (S k))

main : IO ()
main = printProfilingInfo (snd (runProfile (createTyRE length) (pack $ string length)))



