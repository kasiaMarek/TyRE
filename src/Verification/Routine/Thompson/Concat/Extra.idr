module Verification.Routine.Thompson.Concat.Extra

import Data.Vect
import Data.List
import Data.List.Elem

import Core
import NFA
import NFA.Thompson
import Verification.AcceptingPath
import Extra

public export
notPrf1 : (s : a) -> Not (CTh1 s = CEnd)
notPrf1 s prf = absurd prf

public export
notPrf2 : (s : a) -> Not (CTh2 s = CEnd)
notPrf2 s prf = absurd prf

public export
notPrf3 : (s : a) -> Not (CTh1 s = CTh2 s')
notPrf3 s prf = absurd prf

public export
record AboutAddingData a b c where
  constructor MkAboutAddingData
  oldStates: List c
  rout1: Vect (length oldStates) Routine
  accept: c -> Bool
  conv: c -> (CState a b)
  newStart: List (CState a b)
  rout2: Vect (length newStart) Routine

public export
forAcceptingAddNewStart' : AboutAddingData a b c -> (states: List (CState a b) ** Vect (length states) Routine)
forAcceptingAddNewStart' d = forAcceptingAddNewStart d.oldStates d.rout1 d.accept d.conv d.newStart d.rout2

public export
aboutAddingStatesNew : (d : AboutAddingData a b c)
                        -> (state: (CState a b))
                        -> (prf1: state `Elem` fst (forAcceptingAddNewStart d.oldStates d.rout1 d.accept d.conv d.newStart d.rout2))
                        -> (oldState : c)
                        -> ((x : c) -> (y : c) -> (d.conv x = d.conv y) -> (x = y))
                        -> (d.conv oldState = state)
                        -> (Not (state `Elem` d.newStart))
                        -> (prf: oldState `Elem` d.oldStates ** extractBasedOnFst (fst $ forAcceptingAddNewStart d.oldStates d.rout1 d.accept d.conv d.newStart d.rout2) (snd $ forAcceptingAddNewStart d.oldStates d.rout1 d.accept d.conv d.newStart d.rout2) state prf1 = extractBasedOnFst d.oldStates d.rout1 oldState prf)

aboutAddingStatesNew (MkAboutAddingData [] [] accept conv newStart rout2) state prf1 st convInjective prf f = absurd prf1
aboutAddingStatesNew (MkAboutAddingData (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 st convInjective prf f with (accept x) proof p
  aboutAddingStatesNew (MkAboutAddingData (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 st convInjective prf f | True =
    case prf1 of
      Here => (replace {p=(\e => e `Elem` (x::xs))} (sym $ (convInjective _ _ prf)) Here ** Refl)
      (There pos) =>
        let hOrT = hereOrThereExtractBasedOnFst newStart (fst $ forAcceptingAddNewStart xs ys accept conv newStart rout2) (map (y++) rout2) (snd $ forAcceptingAddNewStart xs ys accept conv newStart rout2) state pos
        in case hOrT of
          (Left (pos' ** prf')) => absurd (f pos')
          (Right (pos'** prf')) =>
            let (isElem ** rprf) = aboutAddingStatesNew (MkAboutAddingData xs ys accept conv newStart rout2) state pos' st convInjective prf f
            in (There isElem ** trans prf' rprf)

  aboutAddingStatesNew (MkAboutAddingData (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 st convInjective prf f | False =
    case prf1 of
      Here => (replace {p=(\e => e `Elem` (x::xs))} (sym $ (convInjective _ _ prf)) Here ** Refl)
      (There pos) =>
        let (isElem ** rprf) = aboutAddingStatesNew (MkAboutAddingData xs ys accept conv newStart rout2) state pos st convInjective prf f
        in (There isElem ** rprf)

public export
aboutAddingStatesOld : (d : AboutAddingData a b c)
                        -> (state: (CState a b))
                        -> (prf1: state `Elem` fst (forAcceptingAddNewStart d.oldStates d.rout1 d.accept d.conv d.newStart d.rout2))
                        -> ((oldState: c) -> Not (d.conv oldState = state))
                        -> (oldState : c ** (prf: oldState `Elem` d.oldStates ** (prf2: state `Elem` d.newStart ** (d.accept oldState = True, extractBasedOnFst (fst $ forAcceptingAddNewStart d.oldStates d.rout1 d.accept d.conv d.newStart d.rout2) (snd $ forAcceptingAddNewStart d.oldStates d.rout1 d.accept d.conv d.newStart d.rout2) state prf1 = extractBasedOnFst d.oldStates d.rout1 oldState prf ++ extractBasedOnFst d.newStart d.rout2 state prf2))))

aboutAddingStatesOld (MkAboutAddingData [] [] accept conv newStart rout2) state prf1 f = absurd prf1
aboutAddingStatesOld (MkAboutAddingData (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 f with (accept x) proof p
  aboutAddingStatesOld (MkAboutAddingData (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 notPrf | True =
    case prf1 of
      Here => absurd (notPrf x Refl)
      (There pos) =>
        let hOrT = hereOrThereExtractBasedOnFst newStart (fst $ forAcceptingAddNewStart xs ys accept conv newStart rout2) (map (y++) rout2) (snd $ forAcceptingAddNewStart xs ys accept conv newStart rout2) state pos
        in case hOrT of
          (Left (pos' ** prf)) => (x ** (Here ** (pos' ** (p, trans prf (mapExtractBasedOnFst _ _ _ _ _)))))
          (Right (pos'** prf)) =>
              let (os ** (opos ** (npos ** (acc, eQ)))) = aboutAddingStatesOld (MkAboutAddingData xs ys accept conv newStart rout2) state pos' notPrf
              in (os ** (There opos ** (npos ** (acc, trans prf eQ))))

  aboutAddingStatesOld (MkAboutAddingData (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 notPrf | False =
    case prf1 of
      Here => absurd (notPrf x Refl)
      (There pos) =>
        let (os ** (opos ** (npos ** (acc, eQ)))) = aboutAddingStatesOld (MkAboutAddingData xs ys accept conv newStart rout2) state pos notPrf
        in (os ** (There opos ** (npos ** (acc, eQ))))
