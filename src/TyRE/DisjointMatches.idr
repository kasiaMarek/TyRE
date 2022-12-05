module TyRE.DisjointMatches

import Data.SnocList
import Data.List

infix 6 :+:,.+.
infix 7 :<,::

||| A data structure to represent succesful (disjoint) matches in a string.
||| A string is written here as alternatating sequence of substring and matches.
||| E.g. the string "aaadeebbjk" matched against r "((a*d)|(bb))!" is represented as
||| Snoc (Snoc (Prefix []) (Just 3) ['e', 'e']) Nothing ['j','k']
||| Similar: DisjointMatches
public export
data DisjointMatchesSnoc : Type -> Type where
  Prefix : SnocList Char -> DisjointMatchesSnoc a
  Snoc   : DisjointMatchesSnoc a -> a -> SnocList Char -> DisjointMatchesSnoc a

export
(:<) : DisjointMatchesSnoc a -> Char -> DisjointMatchesSnoc a
(:<) (Prefix cs) c            = Prefix (cs :< c)
(:<) (Snoc dm parseTree cs) c = Snoc dm parseTree (cs :< c)

export
(:+:) : DisjointMatchesSnoc a -> a -> DisjointMatchesSnoc a
(:+:) dm parseTree = Snoc dm parseTree [<]

||| A data structure to represent succesful (disjoint) matches in a string.
||| A string is written here as alternatating sequence of substring and matches.
||| E.g. the string "aaadeebbjk" matched against r "((a*d)|(bb))!" is represented as
||| Cons [] (Just 3) (Cons ['e', 'e'] Nothing (Suffix ['j','k']))
||| Similar: DisjointMatchesSnoc
public export
data DisjointMatches : Type -> Type where
  Suffix : List Char -> DisjointMatches a
  Cons : List Char -> a -> DisjointMatches a -> DisjointMatches a

export
(::) : DisjointMatches a -> Char -> DisjointMatches a
(::) (Suffix cs) c = Suffix (c :: cs)
(::) (Cons cs parse tail) c = Cons (c :: cs) parse tail

export
(.+.) : a -> DisjointMatches a -> DisjointMatches a
(.+.) parse dm = Cons [] parse dm

export
(<>>) : DisjointMatchesSnoc a -> DisjointMatches a -> DisjointMatches a
(<>>) (Prefix sc)      (Suffix cs)    = Suffix (sc <>> cs)
(<>>) (Prefix sc)      (Cons cs p tl) = Cons (sc <>> cs) p tl
(<>>) (Snoc nck p sc)  (Suffix cs)    = nck <>> Cons [] p (Suffix (sc <>> cs))
(<>>) (Snoc nck p sc)  (Cons cs q tl) = nck <>> Cons [] p (Cons (sc <>> cs) q tl)

export
(<><) : DisjointMatchesSnoc a  -> DisjointMatches a -> DisjointMatchesSnoc a
(<><) (Prefix sc)     (Suffix cs)    = Prefix (sc <>< cs)
(<><) (Snoc nck p sc) (Suffix cs)    = Snoc nck p (sc <>< cs)
(<><) (Prefix sc)     (Cons cs p tl) = Snoc (Prefix (sc <>< cs)) p [<] <>< tl
(<><) (Snoc nck p sc) (Cons cs q tl) = Snoc (Snoc nck p (sc <>< cs)) q [<] <>< tl

public export
Cast (DisjointMatchesSnoc a) (DisjointMatches a) where
  cast sx = sx <>> (Suffix [])

public export
Cast (DisjointMatches a) (DisjointMatchesSnoc a) where
  cast xs = (Prefix [<]) <>< xs

public export
Functor DisjointMatches where
  map f (Suffix cs) = Suffix cs
  map f (Cons cs parse tail) = Cons cs (f parse) (map f tail)

public export
Functor DisjointMatchesSnoc where
  map f (Prefix sc) = Prefix sc
  map f (Snoc neck parse sc) = Snoc (map f neck) (f parse) sc

export
toString : (a -> String) -> DisjointMatches a -> String
toString f (Suffix cs) = pack cs
toString f (Cons cs parse tail) = (pack cs) ++ (f parse) ++ (toString f tail)

export
toStringSnoc : (a -> String) -> DisjointMatchesSnoc a -> String
toStringSnoc f (Prefix sc) = pack (cast sc)
toStringSnoc f (Snoc neck parse sc) = (toStringSnoc f neck) ++ (f parse) ++ pack (cast sc)

export
Show a => Show (DisjointMatches a) where
  show (Suffix cs) = pack cs
  show (Cons cs pt tail) = pack cs ++ "~~" ++ show pt ++ "~~" ++ show tail

export
Show a => Show (DisjointMatchesSnoc a) where
  show (Prefix cs) = pack $ toList cs
  show (Snoc neck pt cs) = show neck ++ "~~" ++ show pt ++ "~~" ++ pack (toList cs)

export
length : DisjointMatches a -> Nat
length (Suffix _)       = Z
length (Cons _ _ tail)  = S (length tail)
