module Profiling.NFA

import NFA
import Evidence
import Extra.Reflects

public export
ProfilingInfo : (nfa : NA) -> Type
ProfilingInfo nfa = List (Maybe Char, List $ Thread nfa)

public export
runFromProfile : (nfa: NA) -> Program nfa -> Word -> (tds : List $ Thread nfa) -> (Maybe Evidence, ProfilingInfo nfa)
runFromProfile nfa prog [] tds =  (map (\td => td.vmState.evidence)
                        (findR (\td => nfa .accepting td.naState) tds).Holds,
                        [(Nothing, tds)])
runFromProfile nfa prog (c::cs) tds = 
    let goResult : (Maybe Evidence, ProfilingInfo nfa)
        goResult = runFromProfile nfa prog cs $ runMain c tds
    in (fst goResult, (Just c, tds) :: snd goResult)

public export
runAutomatonProfile : (nfa: NA) -> Program nfa -> Word -> (Maybe Evidence, ProfilingInfo nfa)
runAutomatonProfile nfa prog word = runFromProfile nfa prog word initialise