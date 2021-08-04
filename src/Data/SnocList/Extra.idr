module Data.SnocList.Extra

import Data.SnocList

public export
appendAssociative : {a : Type} -> {x,y,z : SnocList a} -> x ++ (y ++ z) = (x ++ y) ++ z
appendAssociative {x, y, z=[<]} = Refl
appendAssociative {x, y, z=(sz :< z')} = cong (:< z') (appendAssociative {x, y, z=sz})

public export
appendNilLeftNeutral  : {a : Type} -> {x : SnocList a} -> [<] ++ x = x
appendNilLeftNeutral {x = [<]} = Refl
appendNilLeftNeutral {x = (sx :< x)} = cong (:< x) (appendNilLeftNeutral {x = sx})

public export
replicate : Nat -> (elem : a) -> SnocList a
replicate 0 elem = [<]
replicate (S k) elem = (replicate k elem) :< elem

export
replicateForSucc  : (k : Nat) -> (elem : a) 
                  -> (replicate (S k) elem = [< elem] ++ replicate k elem)
replicateForSucc 0 elem = Refl
replicateForSucc (S k) elem = cong (:< elem) (replicateForSucc k elem)
