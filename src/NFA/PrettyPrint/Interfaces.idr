module NFA.PrettyPrint.Interfaces

import NFA
import Data.List
import NFA.Thompson

public export
interface Ordered ty where
  constructor MkOrdered
  all : List ty

public export
Ordered PState where
  all = [StartState, AcceptState]

public export
Ordered AState where
  all = [ASt]

public export
Ordered a => Ordered b => Ordered (CState a b) where
  all = CEnd::(map CTh1 all) ++ (map CTh2 all)

public export
Show PState where
  show StartState = "S"
  show AcceptState = "A"

public export
Show AState where
  show a = "N"

public export
Show a => Show b => Show (CState a b) where
  show (CTh1 s) = show s ++ "1"
  show (CTh2 s) = show s ++ "2"
  show CEnd = "E"
