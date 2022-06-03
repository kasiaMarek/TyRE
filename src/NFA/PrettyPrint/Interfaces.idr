module NFA.PrettyPrint.Interfaces

import NFA
import Data.List
import Thompson

public export
interface Ordered ty where
  constructor MkOrdered
  all : List ty

public export
Ordered BaseStates where
  all = [StartState, AcceptState]

public export
Ordered Unit where
  all = [()]

public export
Ordered a => Ordered b => Ordered (Either a b) where
  all = (map Left all) ++ (map Right all)

public export
Show BaseStates where
  show StartState = "S"
  show AcceptState = "A"
