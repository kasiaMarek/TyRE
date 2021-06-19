module Verification.Thompson.Concat

import Data.SnocList
import Data.Vect
import Data.List
import Data.List.Elem

import Codes
import Core
import NFA
import NFA.Thompson
import Evidence
import Verification.AcceptingPath
import Extra
import Extra.Reflects
import Data.Vect

%default total

data ConcatPhase = Th1P | Th2P

0 proofForPhase : (re1 : CoreRE) -> (re2 : CoreRE) -> (phase : ConcatPhase) -> (td1 : Thread (thompson re1).nfa) -> (mtd2 : Maybe $ Thread (thompson re2).nfa)
                  -> (td : Thread (thompson $ Concat re1 re2).nfa) -> (acc: AcceptingFrom (thompson $ Concat re1 re2).nfa td.naState word) -> Type

proofForPhase re1 re2 Th1P td1 mtd2 td acc = (td.naState = CTh1 td1.naState, td.vmState.evidence = td1.vmState.evidence)
proofForPhase re1 re2 Th2P td1 mtd2 td acc = (td2: Thread (thompson re2).nfa ** (mtd2 = Just td2, td.naState = CTh2 td2.naState, td.vmState.evidence = td1.vmState.evidence ++ td2.vmState.evidence))

0 resultForPhase : (re1 : CoreRE) -> (re2 : CoreRE) -> (phase : ConcatPhase) -> (td1 : Thread (thompson re1).nfa) -> (mtd2 : Maybe $ Thread (thompson re2).nfa)
                  -> (td : Thread (thompson $ Concat re1 re2).nfa) -> (acc: AcceptingFrom (thompson $ Concat re1 re2).nfa td.naState word) -> Type

resultForPhase re1 re2 Th1P td1 mtd2 td acc = (word': Word ** (acc2: Accepting (thompson re2).nfa word' ** (word'': Word ** (acc1: AcceptingFrom (thompson re1).nfa td1.naState word'' **
                                                    (extractEvidenceFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} td acc =
                                                        extractEvidenceFrom {nfa = (thompson re1).nfa, prog = (thompson re1).prog} td1 acc1 ++
                                                        extractEvidence {nfa = (thompson re2).nfa, prog = (thompson re2).prog} acc2 ++
                                                        [< PairMark]
                                                      )
                                                    ))))

resultForPhase re1 re2 Th2P td1 mtd2 td acc = (word': Word ** (td2 : Thread (thompson re2).nfa ** (acc2: AcceptingFrom (thompson re2).nfa td2.naState word' **
                                                    (extractEvidenceFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} td acc =
                                                        td1.vmState.evidence ++
                                                        extractEvidenceFrom {nfa = (thompson re2).nfa, prog = (thompson re2).prog} td2 acc2 ++
                                                        [< PairMark]
                                                      )
                                                    )))

evidenceForConcat : {re1 : CoreRE} -> {re2 : CoreRE} -> (phase : ConcatPhase) -> (td : Thread (thompson $ Concat re1 re2).nfa)
                  -> (acc: AcceptingFrom (thompson $ Concat re1 re2).nfa td.naState word)
                  -> (mtd2 : Maybe $ Thread (thompson re2).nfa)
                  -> (td1 : Thread (thompson re1).nfa)
                  -> (proofForPhase re1 re2 phase td1 mtd2 td acc) -> (resultForPhase re1 re2 phase td1 mtd2 td acc)

--TODO: proof impossible `prf + stEq1`
evidenceForConcat Th1P td (Accept td.naState prf) mtd2 td1 (stEq1, evEq1) = ?absr0
--TODO: proof impossible `prf1`
evidenceForConcat Th1P td (Step td.naState c CEnd prf1 (Accept CEnd Refl)) mtd2 td1 (stEq1, evEq1) = ?absr1

evidenceForConcat Th1P td (Step td.naState c t prf1 (Step t c' s prf2 acc)) mtd2 td1 (stEq1, evEq1) = ?kkkk

evidenceForConcat Th2P td acc Nothing td1 (td2 ** (prf, stEq2, evEq1)) = absurd prf
evidenceForConcat Th2P td acc (Just td') td1 (td2 ** (prf, stEq2, evEq1)) = ?evidenceForConcat_rhs_2

public export
concatEvidencePrf : (re1 : CoreRE) -> (re2: CoreRE)
                              -> (acc: Accepting (thompson $ Concat re1 re2).nfa word)
                              -> (word' : Word ** (acc1: Accepting (thompson re1).nfa word' ** (word'' : Word ** (acc2: Accepting (thompson re2).nfa word'' **
                                                        (extractEvidence {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} acc) =
                                                            extractEvidence {nfa = (thompson re1).nfa, prog = (thompson re1).prog} acc1 ++
                                                            extractEvidence {nfa = (thompson re2).nfa, prog = (thompson re2).prog} acc2 ++ [< PairMark]
                                                          ))))
