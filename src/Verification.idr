module Verification

import Pred
import NFA
import Evidence
import Data.List.Elem
import Data.List
import Data.Vect
import Data.Vect.Elem
import Extra
import Extra.Reflects
import Verification.AcceptingPath
import Data.Stream

recordPathHelper : {auto nfa : NA} -> {auto prog: Program nfa} -> (c: Char) -> (td : Thread nfa)
              -> (td': Thread nfa ** (td' `Elem` runMapping c td, (acc: AcceptingFrom nfa td'.naState cs ** extractEvidenceFrom td' acc = ev)))
              -> (acc: AcceptingFrom nfa td.naState (c::cs) ** extractEvidenceFrom td acc = ev)

recordPathHelper c td (td' ** (isElemOfF, (accepts ** isEq))) =
  let (x1 ** (x2 ** (isElem ** (eqToExtractFst, ftd', satQ)))) = mapFSpec
                                              (runFunction c td)
                                              (\e => (td'.naState = fst e))
                                              (\t => (td'.naState = t.naState))
                                              (nfa .next td.naState c)
                                              (prog .next td.naState c)
                                              (\x1 => \x2 => \p => p)
                                              td'
                                              (isElemOfF, Refl)
      isElem' : td'.naState `Elem` (nfa .next td.naState c)
      isElem' = (rewrite satQ in isElem)

      acc : AcceptingFrom nfa td.naState (c::cs)
      acc = Step td.naState c td'.naState isElem' accepts

      prf : (stepOfExtractEvidence td c td'.naState isElem' = td')
      prf = rewrite satQ in rewrite eqToExtractFst in ftd'
  in (acc ** rewrite prf in isEq)

isElemDistinct : {auto nfa : NA} -> {auto prog : Program nfa}
              -> (tds : List (Thread nfa)) -> (td : Thread nfa)
              -> (prf : td `Elem` distinct tds)
              -> (td `Elem` tds)

isElemDistinct [] td prf = absurd prf
isElemDistinct (t :: tds) td prf with (nfa .isEq)
  isElemDistinct (t :: tds) td prf | _
    with (find (\e => e.naState == t.naState) tds)
    isElemDistinct (t :: tds) t Here | _ | Nothing = Here
    isElemDistinct (t :: tds) td (There pos) | _ | Nothing =
      There (isElemDistinct tds td pos)
    isElemDistinct (t :: tds) td pos | _ | (Just _) =
      There (isElemDistinct tds td pos)

0 recordPath : {auto nfa : NA} -> {auto prog : Program nfa} -> (tds : List (Thread nfa)) -> (str : Word)
          -> (prf : runFrom str tds = Just ev)
          -> (td : Thread nfa ** (td `Elem` tds, (acc: AcceptingFrom nfa td.naState  str ** extractEvidenceFrom td acc = ev)))

recordPath tds [] prf with (findR (\td => nfa.accepting td.naState) tds)
  recordPath tds [] prf | (Nothing `Because` (Otherwise f)) = absurd prf
  recordPath tds [] prf | ((Just x) `Because` (Indeed (pos, isEq))) = (x ** (pos, (Accept x.naState isEq ** justInjective prf)))

recordPath {nfa} tds (c :: cs) prf =
  let (td' ** (pos', (acc' ** isEq'))) = recordPath _ cs prf
      (x ** (isElem, satQ , _)) =
        bindSpec
          (runMapping c)
          (\e => (acc: AcceptingFrom nfa e.naState cs ** extractEvidenceFrom e acc = ev))
          (\e => (acc: AcceptingFrom nfa e.naState (c :: cs) ** extractEvidenceFrom e acc = ev))
          (recordPathHelper c)
          tds
          (td' ** (isElemDistinct _ _ pos', (acc' ** isEq')))
  in (x ** (isElem, satQ))

public export
0 extractEvidenceEquality : (nfa : NA)
                        -> (prog : Program nfa)
                        -> (str : Word)
                        -> (ev : Evidence)
                        -> (prf : runAutomaton str = Just ev)
                        -> (acc: Accepting nfa str ** extractEvidence acc = ev)

extractEvidenceEquality nfa prog str ev prf =
  let (td ** (pos, (acc ** eq))) = recordPath (NFA.initialise) str prf
      (x1 ** (x2 ** (isElem ** (eqToExtractFst, ftd', satQ)))) = mapFSpec
                                                                  (initFuction)
                                                                  (\e => (td.naState = fst e))
                                                                  (\t => (td.naState = t.naState))
                                                                  (nfa .start)
                                                                  (prog .init)
                                                                  (\x1 => \x2 => \p => p)
                                                                  td
                                                                  (pos, Refl)
      acc' : AcceptingFrom nfa x1 str
      acc' = replace {p=(\s => AcceptingFrom nfa s str)} satQ acc

      isElem' : td.naState `Elem` nfa.start
      isElem' = replace {p=(\s => s `Elem` nfa.start)} (sym satQ) isElem

      prf : (extractEvidenceInitialStep td.naState isElem' = td)
      prf = rewrite satQ in rewrite eqToExtractFst in ftd'

  in (Start td.naState isElem' acc ** rewrite prf in eq)


0 eqForStreamFrom : (nfa : NA)
                  -> (prog : Program nfa)
                  -> (stm : Stream Char)
                  -> (tds : List (Thread nfa))
                  -> (str : Word ** runFrom str tds = runFromStream stm tds)
eqForStreamFrom nfa prog stm []   = ([] ** Refl)
eqForStreamFrom nfa prog (c::cs) (t::tds) with (findR (\td => nfa.accepting td.naState) (t::tds)) proof p
  eqForStreamFrom nfa prog (c::cs) (t::tds) | ((Just x) `Because` _) = ([] ** rewrite p in Refl)
  eqForStreamFrom nfa prog (c::cs) (t::tds) | (Nothing `Because` _) =
    let nextTds : List (Thread nfa)
        nextTds = runMain c (t::tds)
        rest : (str : Word ** runFrom str nextTds = runFromStream cs nextTds)
        rest = eqForStreamFrom nfa prog cs nextTds
        (wordTail ** eqRest) := rest
    in (c::wordTail ** eqRest)

public export
0 eqForStream : (nfa : NA)
              -> (prog : Program nfa)
              -> (stm : Stream Char)
              -> (str : Word ** runAutomaton str = runAutomatonStream stm)
eqForStream nfa prog stm = eqForStreamFrom nfa prog stm initialise
