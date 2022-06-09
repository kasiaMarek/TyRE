module Verification.Thompson.Concatenation

import Core
import Thompson
import NFA
import Evidence
import Extra

import Verification.AcceptingPath
import Verification.Routine

import Data.SnocList
import Data.List.Elem

-- thompsonConcat : (re1, re2 : CoreRE)
--             -> (acc : Accepting (smToNFA (thompson (Concat re1 re2))) word)
--             -> (mcvm  : (Maybe Char, VMState))
--             -> ((acc1 : Accepting (smToNFA (thompson re1)) word1, acc2 : Accepting (smToNFA (thompson re2)) word2) ** 
--                 (executeRoutineFrom (extractRoutine {sm = (thompson (Concat re1 re2))} acc) mcvm
--             --             = (snd mcvm).evidence ++ ev, ev `Encodes` [< Right $ ShapeCode (Concat re1 re2)]))
--             -- -> (ev  : Evidence
--             --     ** (executeRoutineFrom (extractRoutine {sm = (thompson (Concat re1 re2))} acc) mcvm
--             --             = (snd mcvm).evidence ++ ev, ev `Encodes` [< Right $ ShapeCode (Concat re1 re2)]))