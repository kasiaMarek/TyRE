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

recordPathHelper : {auto sm: SM} -> (c: Char) -> (td : Thread sm.State)
              -> (td': Thread sm.State ** (td' `Elem` runMapping c td, (acc: AcceptingFrom (smToNFA sm) td'.naState cs ** extractEvidenceFrom td' acc = ev)))
              -> (acc: AcceptingFrom (smToNFA sm) td.naState (c::cs) ** extractEvidenceFrom td acc = ev)

recordPathHelper c td (td' ** (isElemOfF, (accepts ** isEq))) =
  let (x1 ** (x2 ** (isElem ** (eqToExtractFst, ftd', satQ)))) = mapSpec
                                              (runFunction c td)
                                              (\e => (td'.naState = fst e))
                                              (\t => (td'.naState = t.naState))
                                              (sm .next td.naState c)
                                              (\x1 => \x2 => \p => p)
                                              td'
                                              (isElemOfF, Refl)
      isElem' : td'.naState `Elem` ((smToNFA sm).next td.naState c)
      isElem' = (rewrite satQ in isElem)

      acc : AcceptingFrom (smToNFA sm) td.naState (c::cs)
      acc = Step {nfa = (smToNFA sm)} td.naState c td'.naState isElem' accepts

      prf : (stepOfExtractEvidence td c td'.naState isElem' = td')
      prf = rewrite satQ in rewrite eqToExtractFst in ftd'
  in (acc ** rewrite prf in isEq)

isElemDistinct : {auto sm : SM}
              -> (tds : List (Thread sm.State)) 
              -> (td : Thread sm.State)
              -> (prf : td `Elem` distinct {eq = sm.isEq} tds)
              -> (td `Elem` tds)

isElemDistinct [] td prf = absurd prf
isElemDistinct {sm} (t :: tds) td prf with (sm.isEq) proof p | (find (\e => e.naState == t.naState) tds)
  isElemDistinct {sm} (t :: tds) t Here | _ | Nothing = Here
  isElemDistinct {sm} (t :: tds) td (There pos) | eq | Nothing =
    There (isElemDistinct tds td (rewrite p in pos))
  isElemDistinct {sm} (t :: tds) td pos | _ | (Just _) =
    There (isElemDistinct tds td (rewrite p in pos))

0 recordPath : {auto sm : SM} -> (tds : List (Thread sm.State)) -> (str : Word)
          -> (prf : runFrom str tds = Just ev)
          -> (td : Thread sm.State ** (td `Elem` tds, (acc: AcceptingFrom (smToNFA sm) td.naState  str ** extractEvidenceFrom td acc = ev)))

recordPath tds [] prf with (findR (\td => (smToNFA sm).accepting td.naState) tds)
  recordPath tds [] prf | (Nothing `Because` (Otherwise f)) = absurd prf
  recordPath tds [] prf | ((Just x) `Because` (Indeed (pos, isEq))) = (x ** (pos, (Accept {nfa = (smToNFA sm)} x.naState isEq ** injective prf)))

recordPath {sm} tds (c :: cs) prf =
  let (td' ** (pos', (acc' ** isEq'))) = recordPath _ cs prf
      (x ** (isElem, satQ , _)) =
        bindSpec
          (runMapping c)
          (\e => (acc: AcceptingFrom (smToNFA sm) e.naState cs ** extractEvidenceFrom e acc = ev))
          (\e => (acc: AcceptingFrom (smToNFA sm) e.naState (c :: cs) ** extractEvidenceFrom e acc = ev))
          (recordPathHelper c)
          tds
          (td' ** (isElemDistinct _ _ pos', (acc' ** isEq')))
  in (x ** (isElem, satQ))

public export
0 extractEvidenceEquality : (sm : SM)
                        -> (str : Word)
                        -> (ev : Evidence)
                        -> (prf : runAutomaton str = Just ev)
                        -> (acc: Accepting (smToNFA sm) str ** extractEvidence acc = ev)

extractEvidenceEquality sm str ev prf =
  let (td ** (pos, (acc ** eq))) = recordPath (NFA.initialise) str prf
      (x1 ** (x2 ** (isElem ** (eqToExtractFst, ftd', satQ)))) = mapSpec
                                                                  (initFuction)
                                                                  (\e => (td.naState = fst e))
                                                                  (\t => (td.naState = t.naState))
                                                                  (sm .start)
                                                                  (\x1 => \x2 => \p => p)
                                                                  td
                                                                  (pos, Refl)
      acc' : AcceptingFrom (smToNFA sm) x1 str
      acc' = replace {p=(\s => AcceptingFrom (smToNFA sm) s str)} satQ acc

      isElem' : td.naState `Elem` (smToNFA sm).start
      isElem' = replace {p=(\s => s `Elem` (smToNFA sm).start)} (sym satQ) isElem

      prf : (extractEvidenceInitialStep td.naState isElem' = td)
      prf = rewrite satQ in rewrite eqToExtractFst in ftd'

  in (Start {nfa = (smToNFA sm)} td.naState ?l acc ** ?k)


0 eqForStreamFrom :  (sm : SM)
                  -> (stm : Stream Char)
                  -> (tds : List (Thread sm.State))
                  -> (str : Word ** runFrom str tds = runFromStream stm tds)
eqForStreamFrom sm stm []   = ([] ** Refl)
eqForStreamFrom sm (c::cs) (t::tds) with (findR (\td => sm.accepting td.naState) (t::tds)) proof p
  eqForStreamFrom sm (c::cs) (t::tds) | ((Just x) `Because` _) = ([] ** rewrite p in Refl)
  eqForStreamFrom sm (c::cs) (t::tds) | (Nothing `Because` _) =
    let nextTds : List (Thread sm.State)
        nextTds = runMain c (t::tds)
        rest : (str : Word ** runFrom str nextTds = runFromStream cs nextTds)
        rest = eqForStreamFrom sm cs nextTds
        (wordTail ** eqRest) := rest
    in (c::wordTail ** eqRest)

public export
0 eqForStream :  (sm : SM)
              -> (stm : Stream Char)
              -> (str : Word ** runAutomaton str = runAutomatonStream stm)
eqForStream sm stm = eqForStreamFrom sm stm initialise
