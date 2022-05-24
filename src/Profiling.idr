module Profiling

import Profiling.NFA
import NFA
import NFA.Thompson

--- printing
threadToString : {nfa : NA} -> {auto showState : Show nfa.State} -> Thread nfa -> String
threadToString (MkThread naState vmState) = show naState

stepToString : {nfa : NA} -> {auto showState : Show nfa.State} -> (Maybe Char, List $ Thread nfa) -> String
stepToString (Nothing, threads) = "_ --> " ++ (show $ map threadToString threads)
stepToString (Just c, threads) = (show c) ++ " --> " ++ (show $ map threadToString threads)

export
printProfilingInfo : {nfa : NA} -> {auto showState : Show nfa.State} -> ProfilingInfo nfa -> IO ()
printProfilingInfo [] = printLn ""
printProfilingInfo (x :: xs) = do
    printLn $ stepToString x
    printProfilingInfo xs

--- show for states
export
Show PState where
    show StartState = "StartState"
    show AcceptState = "AcceptState"

export
Show AState where
    show ASt = "ASt"

export
(Show a, Show b) => Show (CState a b) where
    show (CTh1 a) = "CTh1" ++ show a
    show (CTh2 b) = "CTh2" ++ show b
    show CEnd = "CEnd"