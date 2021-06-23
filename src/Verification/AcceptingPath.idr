module Verification.AcceptingPath

import NFA
import Evidence
import Data.List.Elem
import Data.List
import Data.Vect
import Extra

public export
data AcceptingFrom : (nfa : NA) -> (s : nfa.State) -> (word : Word) -> Type where
  Accept : {auto nfa : NA} -> (s : nfa.State) -> (prf : nfa.accepting s = True) -> AcceptingFrom nfa s []
  Step   : {auto nfa : NA} -> (s : nfa.State) -> (c : Char) -> (t : nfa.State)
        -> (prf : t `Elem` (nfa.next s c))
        -> AcceptingFrom nfa t w
        -> AcceptingFrom nfa s (c :: w)

public export
data Accepting : (nfa : NA) -> (word : Word) -> Type where
  Start : {auto nfa : NA} -> (s : nfa.State) -> (prf : s `Elem` nfa.start) -> AcceptingFrom nfa s w
       -> Accepting nfa w

public export
stepOfExtractEvidence  : {auto nfa : NA}
                      -> {auto prog : Program nfa}
                      -> (td : Thread nfa)
                      -> (c : Char)
                      -> (s : nfa .State)
                      -> (prf: s `Elem` nfa .next td.naState c)
                      -> (Thread nfa)

stepOfExtractEvidence td c s prf =
 let r : Routine
     r = extractBasedOnFst (nfa .next td.naState c) (prog .next td.naState c) s prf
 in runFunction c td (s,r)

public export
extractEvidenceFrom : {auto nfa : NA} -> {auto prog : Program nfa} -> (td : Thread nfa) -> AcceptingFrom nfa td.naState word -> Evidence
extractEvidenceFrom td (Accept td.naState prf) = td.vmState.evidence
extractEvidenceFrom td (Step {w} td.naState c s prf acc) = extractEvidenceFrom (stepOfExtractEvidence td c s prf) acc

public export
extractEvidenceInitialStep : {auto nfa : NA} -> {auto prog : Program nfa}
                          -> (s : nfa .State) -> (prf: s `Elem` nfa .start)
                          -> (Thread nfa)

extractEvidenceInitialStep s prf =
  let r : Routine
      r = extractBasedOnFst (nfa .start) (prog .init) s prf
  in initFuction (s,r)

public export
extractEvidence : {auto nfa : NA} -> {auto prog : Program nfa} -> Accepting nfa word -> Evidence
extractEvidence (Start {w} s prf acc) =
  let td : Thread nfa
      td = extractEvidenceInitialStep s prf
  in extractEvidenceFrom td acc
