module Verification.Thompson.Predicate

import Core
import Thompson
import NFA
import Evidence
import Extra

import Verification.AcceptingPath
import Verification.Routine

import Data.SnocList
import Data.List.Elem

export
thompsonRoutinePrfPredicate : (f : Char -> Bool)
                            -> (acc : Accepting (smToNFA (thompson (Pred f))) word)
                            -> (mcvm  : (Maybe Char, VMState))
                            -> (ev  : Evidence
                                    ** (executeRoutineFrom (extractRoutine {sm = (thompson (Pred f))} acc) mcvm
                                            = (snd mcvm).evidence ++ ev, ev `Encodes` [< Right $ ShapeCode (Pred f)]))

thompsonRoutinePrfPredicate {word = c::cs} f (Start (Just StartState) Here (Step StartState c t prf acc)) mcvm with (f c)
  thompsonRoutinePrfPredicate {word = c::[]} f (Start (Just StartState) Here (Step StartState c Nothing Here Accept)) (mc, vm) | True = ([< CharMark c] ** (Refl, AChar [<] c))
  thompsonRoutinePrfPredicate {word = c::cs} f (Start (Just StartState) Here (Step StartState c s (There prf) acc)) mcvm | True = absurd prf
  thompsonRoutinePrfPredicate {word = c::cs} f (Start (Just StartState) Here (Step StartState c t prf acc)) mcvm | False = absurd prf
thompsonRoutinePrfPredicate f (Start s (There prf) x) mcvm = absurd prf
