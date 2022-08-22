module TyRE.Verification.Thompson.Predicate

import Data.SnocList
import Data.List.Elem

import TyRE.CoreRE
import TyRE.Thompson
import TyRE.NFA
import TyRE.Evidence
import TyRE.Extra

import TyRE.Verification.AcceptingPath
import TyRE.Verification.Routine

export
thompsonRoutinePrfPredicate : (f : Char -> Bool)
                            -> (acc : Accepting (smToNFA (smForPred f)) word)
                            -> (mcvm : (Maybe Char, VMState))
                            -> (ev : Evidence
                                    ** (executeRoutineFrom (extractRoutine {sm = (smForPred f)} acc) mcvm
                                            = (snd mcvm).evidence ++ ev, ev `Encodes` [< Right CharC]))

thompsonRoutinePrfPredicate {word = c::cs} f (Start (Just StartState) Here (Step StartState c t prf acc)) mcvm with (f c)
  thompsonRoutinePrfPredicate {word = c::[]} f (Start (Just StartState) Here (Step StartState c Nothing Here Accept)) (mc, vm) | True = ([< CharMark c] ** (Refl, AChar [<] c))
  thompsonRoutinePrfPredicate {word = c::cs} f (Start (Just StartState) Here (Step StartState c s (There prf) acc)) mcvm | True = absurd prf
  thompsonRoutinePrfPredicate {word = c::cs} f (Start (Just StartState) Here (Step StartState c t prf acc)) mcvm | False = absurd prf
thompsonRoutinePrfPredicate f (Start s (There prf) x) mcvm = absurd prf
