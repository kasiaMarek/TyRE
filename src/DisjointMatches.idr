module DisjointMatches

import Data.SnocList
import Data.List

infix 6 :+:,.+.
infix 7 :<,::

public export
data DisjointMatchesSnoc : Type -> Type where
  Prefix : SnocList Char -> DisjointMatchesSnoc a
  Sonc   : DisjointMatchesSnoc a -> a -> SnocList Char -> DisjointMatchesSnoc a

export
(:<) : DisjointMatchesSnoc a -> Char -> DisjointMatchesSnoc a
(:<) (Prefix cs) c            = Prefix (cs :< c)
(:<) (Sonc dm parseTree cs) c = Sonc dm parseTree (cs :< c)

export
(:+:) : DisjointMatchesSnoc a -> a -> DisjointMatchesSnoc a
(:+:) dm parseTree = Sonc dm parseTree [<]

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
(<>>) (Prefix sc) (Suffix cs) = Suffix (sc <>> cs)
(<>>) (Prefix sc) (Cons cs parse tail) = Cons (sc <>> cs) parse tail
(<>>) (Sonc neck parse sc) tail = neck <>> Cons (cast sc) parse tail

export
(<><) : DisjointMatchesSnoc a  -> DisjointMatches a -> DisjointMatchesSnoc a
(<><) (Prefix sc) (Suffix cs) = Prefix (sc <>< cs)
(<><) (Sonc neck parse sc) (Suffix cs) = Sonc neck parse (sc <>< cs)
(<><) neck (Cons cs parse tail) = (Sonc neck parse (cast cs)) <>< tail

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
  map f (Sonc neck parse sc) = Sonc (map f neck) (f parse) sc

export
toString : (a -> String) -> DisjointMatches a -> String
toString f (Suffix cs) = pack cs
toString f (Cons cs parse tail) = (pack cs) ++ (f parse) ++ (toString f tail)

export
toStringSnoc : (a -> String) -> DisjointMatchesSnoc a -> String
toStringSnoc f (Prefix sc) = pack (cast sc)
toStringSnoc f (Sonc neck parse sc) = (toStringSnoc f neck) ++ (f parse) ++ pack (cast sc)
