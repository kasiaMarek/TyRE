module TyRE.Verification.AcceptingPath

import Data.List.Elem
import Data.List
import Data.Vect

import TyRE.NFA
import TyRE.Evidence
import TyRE.Extra

public export
data AcceptingFrom : (nfa : NA) -> (s : Maybe nfa.State) -> (word : Word) -> Type where
  Accept : {auto nfa : NA} -> AcceptingFrom nfa Nothing []
  Step   : {auto nfa : NA} -> (s : nfa.State) -> (c : Char) -> (t : Maybe nfa.State)
        -> (prf : t `Elem` (nfa.next s c))
        -> AcceptingFrom nfa t w
        -> AcceptingFrom nfa (Just s) (c :: w)

public export
data Accepting : (nfa : NA) -> (word : Word) -> Type where
  Start : {auto nfa : NA} -> (s : Maybe nfa.State) -> (prf : s `Elem` nfa.start) -> AcceptingFrom nfa s w
       -> Accepting nfa w

public export
data Path : (nfa : NA) -> (s : Maybe nfa.State) -> (t : Maybe nfa.State) -> (word : Word) -> Type where
  Here : {auto nfa : NA} -> (s : Maybe nfa.State) -> Path nfa s s []
  Concat : {auto nfa : NA} -> {auto r : Maybe nfa.State}
        -> (s : nfa.State) -> (c : Char) -> (t : Maybe nfa.State)
        -> (prf : t `Elem` (nfa.next s c))
        -> Path nfa r (Just s) w
        -> Path nfa r t (w ++ [c])

public export
data PathFromStart : (nfa : NA) -> (t : Maybe nfa.State) -> (word : Word) -> Type where
  Start' : {auto nfa : NA} -> {auto t : Maybe nfa.State} 
        -> (s : Maybe nfa.State) -> (prf : s `Elem` nfa.start)
        -> Path nfa s t word -> PathFromStart nfa t word

parameters {auto sm : SM}

  public export
  stepOfExtractEvidence  : (td : Thread sm.State)
                        -> (c : Char)
                        -> (s : Maybe sm.State)
                        -> (prf : s `Elem` map Builtin.fst (liftNext sm.next td.naState c))
                        -> (Thread sm.State)

  stepOfExtractEvidence td c s prf =
    runFunction c td (s, extractBasedOnFst (liftNext sm.next td.naState c) prf)

  public export
  extractEvidenceFrom : (td : Thread sm.State) 
                      -> AcceptingFrom (smToNFA sm) td.naState word
                      -> Evidence

  extractEvidenceFrom (MkThread Nothing vm) Accept = vm.evidence
  extractEvidenceFrom (MkThread (Just st) vm) (Step {w} st c s prf acc) =
    extractEvidenceFrom (stepOfExtractEvidence (MkThread (Just st) vm) c s prf) acc

  public export
  extractEvidenceInitialStep  : (s : Maybe sm.State) 
                              -> (prf : s `Elem` map Builtin.fst (sm.start))
                              -> (Thread sm.State)

  extractEvidenceInitialStep s prf = 
    initFuction (s, extractBasedOnFst (sm.start) prf)

  public export
  extractEvidence : Accepting (smToNFA sm) word -> Evidence
  extractEvidence (Start {w} s prf acc) =
    let td : Thread sm.State
        td = extractEvidenceInitialStep s prf
    in extractEvidenceFrom td acc

export
(++) : (Path nfa s t wordNeck) -> (AcceptingFrom nfa t wordTail)
    -> AcceptingFrom nfa s (wordNeck ++ wordTail)
(++) (Here _) acc = acc
(++) (Concat s c t prf path) acc = replace  {p = (AcceptingFrom nfa _)}
                                            (appendAssociative _ _ _)
                                            (path ++ Step s c t prf acc)

export
(+) : (PathFromStart nfa s wordNeck) -> (AcceptingFrom nfa s wordTail)
    -> Accepting nfa (wordNeck ++ wordTail)
(+) (Start' s prf path) acc = Start s prf (path ++ acc)
