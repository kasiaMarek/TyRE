module Verification.Thompson.Group

import Core
import Thompson
import NFA
import Evidence
import Extra
import Extra.Pred

import Verification.AcceptingPath
import Verification.Routine
import Verification.Thompson.Common

import Data.SnocList
import Data.List.Elem

constIdSpec : (xs : List (state, Routine)) -> (isElem : x `Elem` map Builtin.fst (mapRoutine (const []) xs)) -> (extractBasedOnFst (mapRoutine (const []) xs) isElem = [])
constIdSpec ((st, r) :: xs) Here = Refl
constIdSpec (_       :: xs) (There pos) = constIdSpec xs pos

groupRoutinePred : (word : Word) -> (re : CoreRE) -> (s : (thompson re).State) -> ExtendedRoutine -> Type
groupRoutinePred word re s routine = 
    if (thompson re).accepting s 
    then routine === [] 
    else routine === (map Observe word) ++ [Regular EmitString]

thompsonRoutineFromPrfGroup : (re : CoreRE)
                        -> {0 word : Word}
                        -> (s : (thompson (Group re)).State)
                        -> (acc : AcceptingFrom (smToNFA (thompson (Group re))) s word)
                        -> groupRoutinePred word (Group re) s (extractRoutineFrom {sm = thompson (Group re)} acc)
                        
thompsonRoutineFromPrfGroup re s (Accept s prf) with ((thompson re).accepting s)
    thompsonRoutineFromPrfGroup re s (Accept s Refl) | True = Refl
thompsonRoutineFromPrfGroup re s (Step s c t prf acc) with ((thompson re).accepting s) proof p
    thompsonRoutineFromPrfGroup re s (Step s c t prf (Accept t prf1)) | False with ((thompson re).accepting t) proof p'
        thompsonRoutineFromPrfGroup re s (Step s c t prf (Accept t Refl)) | False | True = 
            case (addEndRoutineSpec ((thompson re).accepting) [EmitString] (mapRoutine (const []) ((thompson re) .next s c)) t prf) of
                (isElem ** (Left (isEnd, rw1))) => 
                    let rw2 : ?
                        rw2 = constIdSpec ((thompson re).next s c) isElem
                    in cong (Observe c ::) 
                        (rewrite rw1 in 
                            rewrite rw2 in
                                Refl)
                (_      ** (Right (isEnd, _ ))) => absurd (trans (sym isEnd) p')
    thompsonRoutineFromPrfGroup re s (Step s c t prf (Step t c' u prf' acc)) | False with ((thompson re).accepting t) proof p'
        thompsonRoutineFromPrfGroup re s (Step s c t prf (Step t c' u prf' acc)) | False | False = 
            case (addEndRoutineSpec ((thompson re).accepting) [EmitString] (mapRoutine (const []) ((thompson re) .next s c)) t prf) of
                (_      ** (Left  (isEnd, _  ))) => absurd (trans (sym isEnd) p')
                (isElem ** (Right (isEnd, rw1))) => cong (Observe c ::) (rewrite rw1 in ?lll)
        thompsonRoutineFromPrfGroup re s (Step s c t prf (Step t c' u prf' acc)) | False | True = absurd $ noPathsFromAcceptingState (Group re) t c' p' prf'
    thompsonRoutineFromPrfGroup re s (Step s c t prf acc) | True = absurd $ noPathsFromAcceptingState (Group re) s c p prf


export
thompsonRoutinePrfGroup : (re : CoreRE)
                        -> {0 word : Word}
                        -> (acc : Accepting (smToNFA (thompson (Group re))) word)
                        -> (extractRoutine {sm = thompson (Group re)} acc === map Observe word ++ [Regular EmitString])
                        
thompsonRoutinePrfGroup re {word = []} (Start s isElem (Accept s prf)) = ?thompsonRoutinePrfGroup_rhs_1
thompsonRoutinePrfGroup re {word = (c :: w)} (Start s isElem (Step s c t prf y)) = ?thompsonRoutinePrfGroup_rhs_2


