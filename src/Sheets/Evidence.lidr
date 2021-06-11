> module Sheets.Evidence

Let's start the project! The goal of this sheet is to introduce the
evidence datatype and its extraction function.

This concerns two datatypes:

> import Data.SnocList
> import Codes
> import Syntax.PreorderReasoning
[X] 1. Import the module that defines type code, and replace Code with
the type you defined there. I just copied it from your PR.

-- > data Code =
-- >     CharC
-- >     | PairC Code Code
-- >     | StringC
-- >     | UnitC
-- >     | EitherC Code Code
-- >     | ListC Code
-- >     | MaybeC Code
-- >     | BoolC
-- >     | NatC
--
-- > Sem: Code -> Type
-- > Sem CharC         = Char
-- > Sem (PairC x y)   = (Sem x, Sem y)
-- > Sem StringC       = String
-- > Sem UnitC         = ()
-- > Sem (EitherC x y) = Either (Sem x) (Sem y)
-- > Sem (ListC x)     = List (Sem x)
-- > Sem (MaybeC x)    = Maybe (Sem x)
-- > Sem BoolC         = Bool
-- > Sem NatC          = Nat

Our evidence is going to be a list of markers that we'll construct
when recognising the word. I've included only a couple for
demonstration, but you'll need to add at least a few more, either now
(if you want to guess them) or later, just before the final exercise.

> data EvidenceMarker =
>     StringMark String
>   | PairMark
>   | PredMark  (Char -> Bool)
>   | LeftBranchMark
>   | RightBranchMark
>   | GroupMark
>   | StarMark

> Evidence : Type
> Evidence = SnocList EvidenceMarker

The second datatype is the relation: an evidence encodes a (snoc) list
of types.

> data Encodes : Evidence -> SnocList Code -> Type where
>   Lin : [<] `Encodes` [<]
>   OnlyString
>     : (prf : evs `Encodes` cs) -> (str : String)
>     -> (evs :< StringMark str) `Encodes` cs :< StringC
>   APair
>     : (prf : evs `Encodes` cs)
>    -> (prf1 : ev1 `Encodes` [< c1])
>    -> (prf2 : ev2 `Encodes` [< c2])
>    -> {auto ford : evs' = (evs ++ ev1 ++ ev2) :< PairMark}
>    -> evs' `Encodes` (cs :< PairC c1 c2)

[X] 2. a. Implement Ex1:

> Ex1,Ex2 : Encodes [< StringMark "Hello", StringMark "World", PairMark] [< PairC StringC StringC]
> Ex1 =  APair [<] (OnlyString [<] "Hello") (OnlyString [<] "World")

b. See for yourself that Ex2 below is not a valid proof by inspecting
the hole and trying to fill it with Refl.

> Ex2 = APair [<] (OnlyString [<] "Wrong") (OnlyString [<] "World")
>       {ford = ?hole}

We'll use the following data structure to extract a result out of an evidence:

> record Result (ev : Evidence) (c : Code) (cs : SnocList Code) where
>   constructor MkResult
>   result : Sem c
>   rest   : Evidence
>   0 restValid : rest `Encodes` cs

[X] 3. We'll need this helper function:

> assoc : {a : Type} -> (x,y,z : SnocList a) -> x ++ (y ++ z) = (x ++ y) ++ z
> assoc x y [<] = Refl
> assoc x y (sz :< z) = cong (:< z) (assoc x y sz)

> recontextualise : (prf1 : evs1 `Encodes` cs1)
>                -> (prf2 : evs2 `Encodes` cs2)
>                -> (evs1 ++ evs2) `Encodes` (cs1 ++ cs2)

> recontextualise prf1 [<] = prf1
> recontextualise prf1 (OnlyString prf str) = OnlyString (recontextualise prf1 prf) str
> recontextualise prf1 (APair {ford = eqprf} prf prf2' prf1') =
>    let 0 p: ((evs1 ++ (evs ++ (ev1 ++ ev2))) :< PairMark = ((evs1 ++ evs) ++ (ev1 ++ ev2)) :< PairMark)
>        p = cong (:< PairMark) (assoc evs1 evs (ev1 ++ ev2))
>    in APair (recontextualise prf1 prf) prf2' prf1'
>        {ford = trans (cong (evs1 ++) eqprf) p}

Hint: Gur bayl vagrerfgvat pnfr vf NCnve, jurer lbh'yy arrq na
rdhngvbany cebbs sbe gur vzcyvpvg nethzrag {sbeq}.


[ ] 4. Implement these functions:

> extractResult : (ev : Evidence) -> (0 prf : ev `Encodes` (cs :< c)) -> Result ev c cs
> extract : (ev : Evidence) -> (0 prf : ev `Encodes` [< c]) -> Sem c
