module Verification.Thompson.Alt.Extra

import Data.Vect
import Data.List
import Data.List.Elem

import NFA
import NFA.Thompson

export
cTh1InstElemOfInitTwoAlt  : {0 a : Type} -> (sm : SM) -> (s : a)
                          -> ((CTh1 s) `Elem` (fst $ combineTransitions (initTwoAlt sm))) -> Void
cTh1InstElemOfInitTwoAlt sm s pos with (sm.prog.init)
  cTh1InstElemOfInitTwoAlt sm s pos | i with (sm.nfa.start)
    cTh1InstElemOfInitTwoAlt sm s pos | [] | [] impossible
    cTh1InstElemOfInitTwoAlt sm s pos | (i::is) | (t::ts) with (sm.nfa.accepting t)
      cTh1InstElemOfInitTwoAlt sm s (There pos) | (i::is) | (t::ts) | False =
        cTh1InstElemOfInitTwoAlt sm s pos | is | ts
      cTh1InstElemOfInitTwoAlt sm s (There (There pos)) | (i::is) | (t::ts) | True =
        cTh1InstElemOfInitTwoAlt sm s pos | is | ts

export
cTh2InstElemOfInitOneAlt  : {0 a : Type} -> (sm : SM) -> (s : a)
                          -> ((CTh2 s) `Elem` (fst $ combineTransitions (initOneAlt sm))) -> Void
cTh2InstElemOfInitOneAlt sm s pos with (sm.prog.init)
  cTh2InstElemOfInitOneAlt sm s pos | i with (sm.nfa.start)
    cTh2InstElemOfInitOneAlt sm s pos | [] | [] impossible
    cTh2InstElemOfInitOneAlt sm s pos | (i::is) | (t::ts) with (sm.nfa.accepting t)
      cTh2InstElemOfInitOneAlt sm s (There pos) | (i::is) | (t::ts) | False =
        cTh2InstElemOfInitOneAlt sm s pos | is | ts
      cTh2InstElemOfInitOneAlt sm s (There (There pos)) | (i::is) | (t::ts) | True =
        cTh2InstElemOfInitOneAlt sm s pos | is | ts

export
cTh2InstElemOfNextFromOneAlt : {0 a : Type} -> (sm : SM) -> (s : a)
                            -> (t : sm.nfa.State) -> (c : Char)
                            -> ((CTh2 s) `Elem` (fst $ combineTransitions (nextFromOneAlt sm t c))) -> Void
cTh2InstElemOfNextFromOneAlt sm s t c pos with (sm.prog.next t c)
  cTh2InstElemOfNextFromOneAlt sm s t c pos | r with (sm.nfa.next t c)
    cTh2InstElemOfNextFromOneAlt sm s t c pos | [] | [] impossible
    cTh2InstElemOfNextFromOneAlt sm s t c pos | (r::rs) | (s'::ss) with (sm.nfa.accepting s')
      cTh2InstElemOfNextFromOneAlt sm s t c (There (There pos')) | (r::rs) | (s'::ss) | True =
        cTh2InstElemOfNextFromOneAlt sm s t c pos' | rs | ss
      cTh2InstElemOfNextFromOneAlt sm s t c (There pos') | (r::rs) | (s'::ss) | False =
        cTh2InstElemOfNextFromOneAlt sm s t c pos' | rs | ss

export
cTh1InstElemOfNextFromTwoAlt : {0 a : Type} -> (sm : SM) -> (s : a)
                            -> (t : sm.nfa.State) -> (c : Char)
                            -> ((CTh1 s) `Elem` (fst $ combineTransitions (nextFromTwoAlt sm t c))) -> Void

cTh1InstElemOfNextFromTwoAlt sm s t c pos with (sm.prog.next t c)
  cTh1InstElemOfNextFromTwoAlt sm s t c pos | r with (sm.nfa.next t c)
    cTh1InstElemOfNextFromTwoAlt sm s t c pos | [] | [] impossible
    cTh1InstElemOfNextFromTwoAlt sm s t c pos | (r::rs) | (s'::ss) with (sm.nfa.accepting s')
      cTh1InstElemOfNextFromTwoAlt sm s t c (There (There pos')) | (r::rs) | (s'::ss) | True =
        cTh1InstElemOfNextFromTwoAlt sm s t c pos' | rs | ss
      cTh1InstElemOfNextFromTwoAlt sm s t c (There pos') | (r::rs) | (s'::ss) | False =
        cTh1InstElemOfNextFromTwoAlt sm s t c pos' | rs | ss

export
rforEnd : (pos: CEnd `Elem` [CEnd]) -> (r : Routine)
        -> (extractBasedOnFst {b = Routine} [CEnd] [r] pos = r)
rforEnd Here _ = Refl
rforEnd (There _) _ impossible
