# Sheet 2

In this sheet we develop some helper functions we might need during
the project. Please place them in _this_ repository, but in the
correct subdirectories. If we end-up using them a lot, we can consider
adding them to the stdlib (or if you enjoyed created a PR in the
previous sheet, you're invited to propose a PR to contrib).

> import Data.Nat
> import Data.List
> import Data.List.Elem 
> import Data.List.Elem.Extra
> import Data.DPair
> import Syntax.PreorderReasoning

# Recap

First, a few exercises to reconcile the material from the previous
sheet.

## Data.Void.Extra

[ ] 1. Implement:

> contrapositive : (a -> b) -> Not b -> Not a

## Data.List.Elem.Extra

[ ] 1. Extracts an element from a list if we know it's in that
list. The twist is that we may not actually have the element at
runtime.

> recallElem : (xs : List a) -> x `Elem` xs -> a

[ ] 2. ... and prove that `recallElem` recovers the implicit argument:

> recallCorrect : (xs : List a) -> (pos : x `Elem` xs) -> recallElem xs pos = x


# Stuck terms and equational reasoning

When we program with dependent types, the type-checker evaluates our
terms partially when it needs to check equality of two terms, and the
interpreter will evaluate our terms partially until it gets stuck:

 λΠ> map (+2) [1,?x,3]
 [3, prim__add_Integer ?x 2, 5]

We can use dependent types and pattern-matching to help evaluation get
unstuck. For example:

[ ] 1. In the following example:

> example : (x : Nat) -> (prf : x = 2) -> x + x = 4

a. generate a definition for `example`.
b. inspect the hole.
c. case split on `prf`.
d. fill the hole.

Stuck terms come up quite quickly when we start to prove things (that
is, during verification). They would inevitably show up, though
perhaps later, even if you're not proving, just using dependent types.

To see why understanding stuck terms is important, let's prove the
following useful 'swiss-army knife':

> sak : (x,y,z : Nat) -> x + (y + z) = y + (x + z)

[ ] 2. Generate a definition and:
a. split on the middle argument `y`
b. fill one of the holes, split on the middle argument again
c. keep splitting on the middle argument. Are you getting anywhere?

The reason we're not getting anywhere is that the defintion of
addition is biased, and splits its first argument:

 > λΠ> :printdef plus
 > Prelude.plus : Nat -> Nat -> Nat
 > plus 0 y = y
 > plus (S k) y = S (plus k y)

So if we want the type-checker to help us, we should help it get
unstuck, by splitting on the first argument:

> sak' : (x,y,z : Nat) -> x + (y + z) = y + (x + z) 
> sak' 0 y z = Refl

For the inductive case, we'll use a little library for algebraic
reasoning `:doc Syntax.PreorderReasoning`. It exports 4 functions you
need to know about: `Calc, (|~), (~~), (...)`. Here's how you use it:

> sak' (S k) y z 
>   = Calc $ 
>   |~ 1 + (k + (y + z))
>   ~~ 1 + (y + (k + z)) ...(cong (1+) $ sak' k y z)
>   ~~ y + (1 + (k + z)) ...(sym $ sak' y 1 (k + z))

This can look cryptic at first, so let's go through each part.

`Calc` starts the calculation, and `$` puts parentheses around the
rest of the expression. The rest of the expression constructs a value
in a datatype that represents equational proofs. You can inspect it
using a hole:

 > sak' (S k) y z 
 >   = Calc $ ?hole {- ... -}

   k : Nat
   z : Nat
   y : Nat
------------------------------
hole : FastDerivation (1 + (k + (y + z)))
                      (y + (1 + (k + z)))

(I reformatted it to be more readable.)

`Calc` takes this representation, and turns it into a proof that 
 (1 + (k + (y + z))) = y + (1 + (k + z)), or more generally:

λΠ> :t Calc
Calc : FastDerivation x y -> x = y

Next, we have a sequence of equalities: 

                          -- VVVVVVVVVVVVVVV ignore what's in this column for now
 >  |~ 1 + (k + (y + z))
 >  ~~ 1 + (y + (k + z)) 
 >  ~~ y + (1 + (k + z))

On paper, you might write this like so:

    |- 1 + (k + (y + z))
    = 1 + (y + (k + z)) 
    = y + (1 + (k + z))

and read it out loud: 'proof: 1 + (k + (y + z)) equals 1 + (y + (k + z)) 
equals y + (1 + (k + z)).

The final component is the column with the `...`.  `(...)` is an infix operator, and
we use it to justify to the type-checker that we can make this step:
λΠ> :t (...)
Syntax.PreorderReasoning.... : (0 y : a) -> (0 _ : x = y) -> Step x y

This is ASCII art for a thought-bubble `...( reason )`.

The first step is to apply the equation sak' k y z : k + (y + z) = y + (k + z)
1 + (y + (k + z)) ...(cong (1+) $ sak' k y z) 
  : Step ((1 + (k + (y + z)))) (1 + (y + (k + z)))
here:          ^^^^^^^^^^^^^        ^^^^^^^^^^^^

If you look at it closely, we deconstruct each side of the equation
into a context, \x => 1 + x, or equivalently (1+) or S, and then the
left-hand/right-hand side of the equation (underlined with carettes).

That's what `cong` does:

λΠ> :t cong
Prelude.cong : (0 f : (t -> u)) -> a = b -> f a = f b

so:

λΠ> :t cong S
cong S : ?a = ?b -> S ?a = S ?b

The second step uses symmetry:

λΠ> :t sym
Builtin.sym : (0 _ : x = y) -> y = x

[ ] 3. Implement your own versions `cong'` and `sym'`.

Let's prove that addition is associative, but I'll show you how I do
it in steps:

> plusAssociative' : (a,b,c : Nat) -> a + (b + c) = (a + b) + c
> plusAssociative' 0 b c = ?youTry


Here's a tip for how I do it. I include only the interesting case. 

a. It's quick to turn the hole into the following:

 > plusAssociative' (S k) b c = Calc $
 >   |~ _
 >   ~~ _ ...(?plusAssociative_rhs_2)

b. I then inspect the hole, it tells me what I need to prove, and I
replace the 'don't care' symbols `_` with the lhs/rhs of the equation:

 > plusAssociative' (S k) b c = Calc $
 >   |~ 1 + (k + (b + c)) 
 >   ~~ 1 + ((k + b) + c) ...(?plusAssociative_rhs_2)

c. Then, I write the proof down on paper, and type it in, inserting
holes for each justification. In this case, there is only one step.

d. I justify the holes one by one. At this point I can use 'don't
care', since idris can usually work out the missing parts:

> plusAssociative' (S k) b c = Calc $
>   |~ 1 + (k + (b + c))
>   ~~ 1 + ((k + b) + c) ...(cong (1+) $ plusAssociative' _ _ _)

[ ] 4. Prove that:
a. zero is a right-neutral element w.r.t. addition (see `plusZeroRightNeutral`)
b. addition is commutative (see `:t plusAssociative`).

> plusCommutative' : (a, b : Nat) -> a + b = b + a

[ ] 5. Find the module `Syntax.PreorderReasoning` and try to work out
what's going on. It's only 12 lines of code!


This is a good point to take a break, and come back refreshed to the
next section.


# Views

Equational reasoning can be useful, but as you can guess it's fairly
tedious when all you want is to hack. We can use dependent types and
pattern matching to pass information around that helps the
type-checker get unstuck. `Refl` is a bit like that, as you saw, but
we'll take this idea further.

Foe example, let's look at this data type from `Data.List`:

> ||| 'Positive' evidence that a list is non-empty
> data NonEmpty' : List a -> Type where
>   IsNonEmpty' : (x : a) -> (xs : List a) -> NonEmpty' (x :: xs)

and use this type to define the `head` function for lists:

> head' : (xs : List a) -> (0 nonEmpty : NonEmpty' xs) -> a
  
Instead of matching on `xs`, let's match on `nonEmpty`.

[ ] 1. Do this, and fill the hole.

The data-type `NonEmpty` is called a _view_ of its argument list,
because matching on its values tells us something about the list. It's
like a view of the list from a different angle. (The paper that
introduced this technique is called 'The View from the Left', by
McBride and McKinna.)

Note: we are allowed to split on the runtime irrelevant `nonEmpty`
because its datatype has at most one constructor. This is a useful
trick, so it's in fact a technique:

[ ] 2. Prove that we can always recall that a list is non-empty:
> recallNonEmpty : (0 prf : NonEmpty xs) -> NonEmpty xs

This is not as weird as it may first appear: because the data type
only has one constructor, we don't need to have _any_ bits at runtime
to represent this one constructor, so even if we were allowed to have
a value at runtime, we don't need it.


[ ] 3. "Prove" that a list with an element is non-empty:
> elementNonEmpty : x `Elem` xs -> NonEmpty xs

This style of programming where we think of functions as implication
is well established, and you'll sometimes hear people say that 'proofs
are programs'.

[ ] 4. Read about the datatype `Exists`.

To conclude this section, we'll implement a function that 'inverts' a
map:

> invertMap : (0 f : a -> b) -> y `Elem` (map f xs) -> 
>   Exists {type = a} \x => (x `Elem` xs, f x === y)


[ ] 5. Spend a minute or two understanding this type. If you're still
confused, ask Ohad.
 
Note that neither `f, y, xs` are going to be present at runtime (and
since we have only one proof of equality, `f x = y` may as well be
runtime irrelevant.

So this function will give us the position of the element in `xs` that
got mapped to the given position. (This is going to be the identity
function!)

Let's generate the definition, and add some of the implicit arguments:

 > invertMap {xs} {y} f pos = ?invertMap_rhs

We can't split on `xs` because they're runtime irrelevant, and
splitting `pos` gives weird results and errors. The reason is that the
position tells us that `map f xs` is non-empty, but the typechecker
isn't clever enough to work out that `xs` is non-empty.

So we start with a generalisation of exercise 2:

[ ] 6. Prove that, if we had the list, it would be non-empty:

> elementMapNonEmpty : (xs : List a) -> x `Elem` (map f xs) -> NonEmpty xs

We'll now use this function to implement `invertMap`, by adding
another column with a NonEmpty view:

 > invertMap  {xs} {y} f pos with (recallNonEmpty $ elementMapNonEmpty xs pos)
 >  invertMap {xs} {y} f pos | view = ?he

[ ] 7. Match on the view, and then on the position. There's a bug in
idris curently, and you'll need to rewrite the arguments like so:
 >   invertMap {xs = x :: xs} {y = _} f Here 

[ ] 8. Try to complete the implementation of `invertMap`. Ask Ohad if
it takes you more than 1 hour.

[ ] 9. _Compile_ and run the following constantSpaceInversion,
successively doubling the input size until it takes about 30 seconds
to run. Then look at the process's memory footprint. If we're lucky,
the memory footprint should be constant. It might not be though.

> sandwich : (n : Nat) -> List Nat
> sandwich n = (replicate n 0) ++ [1] ++ (replicate n 0)

> sandwichHasOne : (n : Nat) -> 1 `Elem` sandwich n
> sandwichHasOne n = elemAppRight _ _ Here 

> constantSpaceInversion : (n : Nat) -> 1 `Elem` (sandwich n)
> constantSpaceInversion n = 
>   let pos0 = sandwichHasOne n           -- Count until n + 1
>       pos1 = elemMap (1+) pos0          -- Count until n + 1 again
>   in case invertMap (1+) pos1 of        -- Count until n + 1 again
>     Evidence fst (x, prf) => case prf of
>       Refl => x


This is a good time to pause and maybe go for a walk to think about
what just happened.
