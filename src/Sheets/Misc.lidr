# Miscellaneous topics
> module Sheets.Misc

Several other topics we will need in the project.

> import Decidable.Equality
> import Data.Bool.Decidable
> import Data.Maybe
> import Data.List
> import Data.List.Elem
> import Data.List.Quantifiers
> import Data.Bool
> import Data.Void
> import Syntax.PreorderReasoning

# Type-level Metaprogramming

While idris lets us match on types, I don't advise doing it
usually. First, it might be a little unpredictable, especially if
you're manipulating primitive types that don't have an idris
representation (String, Int, etc.) Second, it will force you to deal
with _all_ types, and usually you only want _some_ types.

In that case, I usually define the types I'm going to use and a
semantics function:

> data Code : Type where
>   Bool : Code
>   Maybe : Code -> Code

> Sem : Code -> Type
> Sem Bool = Bool
> Sem (Maybe code) = Maybe (Sem code)


[X] 1. Implement the `Shape` function from your proposal using a `ShapeCode : RE -> Code` (including the definitions of RE, Code and so on that it needs)

[X] 2. Extend `Code` and `Shape` to deal with the full regexes. We
will use this file in the extension.

[X] 3. Implement a `SimplifyCode : Code -> Code` that tidies up the shape, for example:
   a. ((), c) to c
   b. (Either a a) to a
   c. Either a () and Either () a to Maybe a
   d. Either Void a and Either a Void to a
   and so on.

[ ] 4. Implment
  > ConvertSimplification : (c : Code) -> Sem c -> Sem (SimplifyCode c)

  We will use this in the syntactic sugar extension (if we get to it).

Now comment out the parts dealing with the extension to full regexes,
as we'll work with restricted regexes for now.


# Predicates

In a previous sheet, we mentioned propositions-as-types, where we can
think of types as logical assertions and terms of those types as
proofs of those logical assertions. Extending this idea, we think of:
* terms `p : a -> Type` as predicates
* terms of type `p x` as proofs that `x` has the property `p`
* terms of type `Not (p x)` that is `p x -> Void` as proofs that `x` doesn't have the property `p`.


We can then think of dependent function types as universal quantification:

* `\y => (x : a) -> p x y` as `y holds when for all x we can construct
  a proof of `p x y`.

* \y => (x : a ** p x y)` as `y holds when there exists some x for
  which we can construct a proof of `p x y`.

> infix 3 <->
> ||| If and only if relation between predicates
> record (<->) {a : Type} (p, q : a -> Type) where
>   constructor And
>   If     : (x : a) -> (q x -> p x)
>   onlyIf : (x : a) -> (p x -> q x)


[ ] 1. Implament the following

a. Other propositional connectivies: (/\), (\/), TT

> (/\): {a: Type} -> (p : a -> Type) -> (q : a -> Type) -> ((x : a) -> (p x, q x))
> (\/): {a: Type} -> (p : a -> Type) -> (q : a -> Type) -> ((x : a) -> Either (p x) (q x))
> true: x -> Unit
> false: x -> Void

b. (<->) is an equivalence relation between predicates
> reflexive : (p : a -> Type) -> p <-> p

> symmetric : {p,q : a -> Type} -> p <-> q -> q <-> p

Try to write `transitive` yourself
> transitive : {p,q,r : a -> Type} -> p <-> q -> q <-> r -> p <-> r


> tuple : (a -> Type) -> (a -> Type) -> (a -> Type)
> tuple f g x = (f x, g x)

> prod : {p1, p2, p3, p4 : a -> Type} -> p1 <-> q1 -> p2 <-> q2 ->
>       ((p1 `tuple` p2) <-> (p2 `tuple` p2))

# Records with erased fields

Records (which are syntactic sugar for 1-constructor data types), can
have runtime irrelevant fields.

> infixl 4 //
>
> record RIPair (a, b : Type) where
>   constructor (//)
>   fst   : a
>   0 snd : b

[X] 1. Define a record RIPair : (a, b : Type) -> Type, with (//) as
constructor, and whose second argument is runtime irrelevant.

Hint: Vs lbh pna'g jbex vg bhg, ybbx ng gur arkg frpgvba.

`Data.DPair` has all the variations on the dependently-typed pairs.
The one corresponding to `(//)` is `Subset`.

# Type reflection

Boolean results from functions often reflect some property. We can
encode this relationship using a _reflecting_ type:

λΠ> :doc Reflects
Data.Bool.Decidable.Reflects : Type -> Bool -> Type
  Totality: total
  Constructors:
    RTrue : p -> Reflects p True

    RFalse : Not p -> Reflects p False

This type might seem a bit weird, but it becomes useful when we pack
it together with a boolean:

(These would naturally fit in  `Data.Bool.Decidable.Extra`.)

> ||| A boolean value reflecting a property
> namespace Data.Bool.Decidable
>   record RBool P where
>     constructor Because
>     ||| Does the property hold?
>     Holds : Bool
>     ||| A proof of whether the property holds or not
>     0 Proof : Reflects P Holds
      ^ this field is not present at runtim

We can then define smart constructors that make using `RBool` a bit
like using `Dec`:

> ||| Smart constructor for the true case in `RBool`.
> Yes : {0 p : Type} -> p -> RBool p
> Yes reason = True `Because` RTrue reason

> No : {0 p : Type} -> Not p -> RBool p
> No reason = False `Because` RFalse reason

[X] 1. Implement `No`. (Part of the exercise is to work out its type.)

We will now implement a similar reflection mechanism for the `Maybe`
type, naturally fitting in a module named `Data.Maybe.Decidable`:

> data Reflects : (p : a -> Type) -> (Maybe a) -> Type where
>   Indeed    : {0 p : a -> Type} -> (prf : p x) -> Reflects p (Just x)
>   Otherwise : {0 p : a -> Type} -> (prf : (x : a) -> Not (p x)) -> Reflects p Nothing

[X] 2. Implement the `RMaybe : {a : Type} -> (p : a -> Type) -> Type` as a record.
--> RMaybe : {a : Type} -> (p : a -> Type) -> Type
> record RMaybe {a : Type} p where
>   constructor Because
>   Holds   : Maybe a
>   0 Proof : Reflects p Holds

Functions returning a reflecting optional value guarantee a certain
post-condition. We sometimes need to massage this post-condition into
a different shape in order to use it later. The following function is
useful for that purpose:

> map : {0 p,q : a -> Type} -> p <-> q -> RMaybe p -> RMaybe q
> map iff (Nothing `Because` (Otherwise nprf)) = Nothing `Because` ( Otherwise (\x => \qx => nprf x (iff.If x qx)))
> map iff ((Just x) `Because` (Indeed prf)) = (Just x) `Because` (Indeed (iff.onlyIf x prf))

[X] 3. Implement map.

[X] 4. Implement:

> ||| A version of `Data.List.find` that guarantees the result
> ||| is from the list satisfies the predicate, iff such an element exists.
> findR : {0 a : Type} -> (pred : a -> Bool) -> (xs : List a) ->
>   RMaybe (\x => (x `Elem` xs, pred x = True))

> findR pred [] = Nothing `Because` Otherwise \x => \case (_, _) impossible

> findR pred (x :: xs) with (pred x) proof p
>   findR pred (x :: xs) | True = (Just x) `Because` (Indeed (Here, p))
>   findR pred (x :: xs) | False =
>     let iff: (\y => (y `Elem` (xs), pred y = True)) <-> (\y => (y `Elem` x :: xs,  pred y = True))
>         iff = (\y => (\case
>                      (Here, i) => absurd (trans (sym p) i)
>                      (There e, c) => (e,c)
>                   ))
>               `And`
>               (\_ => (\(e,v) => (There e, v)))
>     in map iff (findR pred xs)

Hint 0: V hfrq n 'cnggrea zngpuvat ynzoqn' pnfr cnggrea vzcbffvoyr va zl fbyhgvba.
Hint 1: V nyfb hfrq n ivrj jvgu n cebbs: `jvgu (cerq l) cebbs c`
Hint 2: Gurer'f n fxryrgba ng gur raq bs gur svyr.

























































Hint for Exercise 4
 > findR  pred    []     = ?h0
 > findR  pred (y :: xs) with (pred y) proof p
 >  findR pred (y :: xs) | False = map iff ?1
 >    where
 >      iff : (\x => (x `Elem` (xs), pred x = True)) <-> (\x => (x `Elem` y :: xs,  pred x = True))
 >      iff = (\x => \case
 >                      foo => ?h2
 >                   )
 >        `And`
 >            (\x, (pos, prf) => ?h3)
 >  findR pred (y :: xs) | True  = ?h4
