module NFA.PrettyPrint.Interfaces

import NFA
import Data.List
import Thompson

public export
interface Ordered ty where
  constructor MkOrdered
  all : List ty

public export
Ordered BaseState where
  all = [StartState]

public export
Ordered Unit where
  all = [()]

public export
Ordered a => Ordered b => Ordered (Either a b) where
  all = (map Left all) ++ (map Right all)

public export
Ordered a => Ordered (Maybe a) where
  all = Nothing :: (map Just all)

public export
Show BaseState where
  show StartState = "S"
