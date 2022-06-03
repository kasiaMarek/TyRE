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

parameters {auto sm : SM}

  public export
  stepOfExtractEvidence  : (td : Thread sm.State)
                        -> (c : Char)
                        -> (s : sm.State)
                        -> (prf: s `Elem` map Builtin.fst (sm.next td.naState c))
                        -> (Thread sm.State)

  stepOfExtractEvidence td c s prf =
    runFunction c td (s, extractBasedOnFst (sm.next td.naState c) prf)

  public export
  extractEvidenceFrom : (td : Thread sm.State) 
                      -> AcceptingFrom (smToNFA sm) td.naState word
                      -> Evidence

  extractEvidenceFrom td (Accept td.naState prf) = td.vmState.evidence
  extractEvidenceFrom td (Step {w} td.naState c s prf acc) =
    extractEvidenceFrom (stepOfExtractEvidence td c s prf) acc

  public export
  extractEvidenceInitialStep  : (s : sm.State) 
                              -> (prf: s `Elem` map Builtin.fst (sm.start))
                              -> (Thread sm.State)

  extractEvidenceInitialStep s prf = 
    initFuction (s, extractBasedOnFst (sm.start) prf)

  public export
  extractEvidence : Accepting (smToNFA sm) word -> Evidence
  extractEvidence (Start {w} s prf acc) =
    let td : Thread sm.State
        td = extractEvidenceInitialStep s prf
    in extractEvidenceFrom td acc
