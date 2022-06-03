module NewThompson.NewToOld

import Data.Vect
import Data.List
import Syntax.PreorderReasoning

import Core
import NFA
import NFA.Thompson
import NewThompson

newStartToNFAStart : List (state, Routine) -> List state
newStartToNFAStart start = map fst start

newStartToProgStart : (start : List (state, Routine))
                    -> Vect (length (newStartToNFAStart start)) Routine
newStartToProgStart start = 
    replace
        {p = \n => Vect n Routine}
        (trans (lengthMap start) (sym (lengthMap start)))
        (fromList (map snd start))

newNextToNFANext : (next : state -> Char -> List (state, Routine))
                -> ((st : state) -> (c : Char) -> List state)
newNextToNFANext next st c = map fst (next st c)

newNextToProgNext : (next : state -> Char -> List (state, Routine)) 
                -> ((st : state) -> (c : Char) -> Vect (length (newNextToNFANext next st c)) Routine)
newNextToProgNext next st c =
    replace
        {p = \n => Vect n Routine}
        (trans (lengthMap (next st c)) (sym (lengthMap (next st c))))
        (fromList (map snd (next st c)))

newToNFA : NewThompson.SM -> NA
newToNFA (MkSM state accepting start next) = 
    MkNFA state accepting (newStartToNFAStart start) (newNextToNFANext next)

newToProg : (sm : NewThompson.SM) -> Program (newToNFA sm)
newToProg (MkSM state accepting start next) = 
    MkProgram (newStartToProgStart start) (newNextToProgNext next)

export
newToOld : NewThompson.SM -> NFA.Thompson.SM
newToOld sm = MkSM (newToNFA sm) (newToProg sm)


||| Proof that new thompson construction gives the same result as the old one.
-- Temp solution so the library can be used.
-- Since NA nad Program contain functions and we can't proof equality on functions it's impossible to proof this.
export
thompsonEqProof : (re : CoreRE) -> (thompson re = newToOld (newThompson re))
thompsonEqProof re = believe_me re


