This is a literate idris2 file, it allows us to write text and code in
the same file.

You can read more about literate programming here:

https://idris2.readthedocs.io/en/latest/reference/literate.html

> module Sheets.FP

The purpose of this sheet is to bring you up to speed with some
functional programming techniques. It can take anything between 1 day
and 2 weeks, but if you feel like you're stuck on any part of it,
please ask Ohad! The goal is to get you up to speed so you could start
the project, there will be plenty of opportunities to stare at hard
problems for a long time in the extensions.

We will start from the basics of a project, and if all goes well, you
will prepare a pull-request to the Idris2 standard library by the end
of the sheet.


# Project set-up

[X] 1. Create a new repository (can be on GitHub, or the University's
GitLab) for the project. If it is private, send Ohad an
invitation. (Username on GitHub: ohad).

Once you do, put a X in the tick-box 4 lines above this line, like so:
[X] 1. Create a new repository ...


[X] 2. Populate the repository with the basic stuff:

a. A README.md file
b. a src/Sheets/ directory containing this file
c. a TODO.md file to help you organise your tasks

# Packages

[X] 1. Try to type-check this file.


Type-checking should fail with an error message like so:


     Module Data.Void not found

This is because `Data.Void` is a module in the Idris2's standard library
`contrib` package, which you will need for your project.

[X] 2. Learn about packages here:

  https://idris2.readthedocs.io/en/latest/reference/packages.html

[X] 3. Set a package file for your project.

If you've done it correctly, this file should now type-check.


# Modules and the REPL

This file uses a few modules from the standard library. I assume your
editor lets you have a REPL - if not, I encourage you to switch to an
editor that supports a REPL.

[X] 1. a. Go to the REPL and hit `:browse Data.List.Elem`, you will see a
summary of the `export`ed functions.

b. hit `:doc Elem`, and you'll see a summary of the `Elem` datatype
(the textual information is called a 'docstring', and it's extracted
from the '|||' comment before the datatype and its constructors.

c. Use `:browse`, `:doc`, and `:printdef` to explore some of the
following modules:

> import Data.Void
> import Data.List
> import Data.List.Elem
> import Data.List.Elem.Extra
> import Decidable.Equality
> import Data.SnocList
> import Data.String

[X] 2. Use the `:s` command to find functions of the type

 < Char -> Int
 < Int -> Char
 < String -> List Char
 < List Char -> String

[X] 3. Implement a rot13 function:
> ||| Does all the heavy lifting.
> rotChar13 : Char -> Char

> rotChar13 x =
>  if (x >= 'a' && x <= 'z') then
>     chr ((ord x - ord 'a' + 13) `mod` 26 + ord 'a')
>  else
>     if (x >= 'A' && x <= 'Z') then
>         chr ((ord x - ord 'A' + 13) `mod` 26 + ord 'A')
>     else x

> rot13 : String -> String
> rot13 s = pack $map rotChar13 (unpack s)
You know you got it right vs lbh pna ernq guvf Fgevat.

[X] 3. If you used `fastPack`, your REPL won't be able to evaluate
Strings. Try it.  (But if you compile your code and run it, it should
work as expected, and a little bit faster on larger strings.)

This is one difference between the REPL, which is an interpreter, and
compiled code. The REPL can deal with incomplete code, for example:

> Incomplete : Nat
> Incomplete = 1 + (2 + ?hole + 4)

> main : IO ()
> main = putStrLn $ show Incomplete

[X] 4. a. Evaluate `Incomplete` in the REPL.
b. Execute `main` in two ways:
  (i) using the `:exec main` command
  (ii) by building a binary file whose main function is `main`.

# Basic Functional Programming

Like all functional languageds, lists are a basic building block in
Idris. A very recent addition to the language are snoc-lists: lists
that go the other way. (Use `:doc SnocList`.) We write snoc-lists like so:

> Count : SnocList Nat
> Count = Lin :< 1 :< 2 :< 3 :< 4

[X] 1. Use `show Count` at the REPL to see a more compact way to write
this.


[X] 2. Find the module `Data.List.Elem`.

In the rest of this sheet, we'll implement a corresponding module for
snoc-lists, and prepare it for a PR to the standard library.

[X] 3. Create the module `Data.SnocList.Elem` (in this code-base). It
should be empty.

[X] 4. Implement the following snoc-list analogues:

 < Elem
 < dropElem
 < elemToNat
 < indexElem
 < elemMap

If you use appropriate docstrings, it will be easier to prepare the
file for PR.


This is a good point to take a break, the next section is a bit long,
and you want to approach it with a fresh mind and plenty of time to
dig into it.




# Equality

When you start using dependent types (and you will, don't worry), the
typechecker will sometimes not see that two types are equal, and you
will need to prove to it that they are.

Here's an example of when equality might come up in
practice. Practical things are often more complex, and this example
has lots of moving parts. Don't worry, we'll get to know all of them
much better later in the project, and by the end of the project you'll
be an expert. But I want you to see a complete picture with all the
moving parts, even if it seems a bit messy.

Let's try and define this function:

> ||| The reverse list has all the elements
> total
> elemInReverse : (xs : List a) -> (pos : x `Elem` xs) -> x `Elem` (reverse xs)

[X] 1. Case split on the position argument (you might need to rename
some of the variables due to name clashes), and look at the two holes:

> elemInReverseKasia : (xs : List a) -> (pos : x `Elem` xs) -> x `Elem` (reverse xs)
> elemInReverseKasia (x :: xs) Here = ?elemInReverseKasia_rhs_1
> elemInReverseKasia (x :: xs) (There p) = ?elemInReverseKasia_rhs_2

## Base case

 <  0 a : Type
 <  0 x : a
 <    xs : List a
 < ------------------------------
 < elemInReverse_rhs_1 : Elem x (reverseOnto [x] xs)

`reverseOnto` is a helper function for `reverse`, and `reverseOnto sx ys`
evaluates to `reverse ys ++ sx`:

 < reverseOnto [3, 2, 1] [4, 5, 6]
 λΠ> [6, 5, 4, 3, 2, 1]

We will use this strategy:

1. convince the typechecker that `reverse xs ++ [x] = reverse (x :: xs)`.
2. convince the typechecker that x `Elem` [x].
3. convince the typechecker that x `Elem` (xs ++ [x])

and then conclude.

This is one way to do it:

> elemInReverse (x :: xs) Here =
>    -- v-- this means step1 is runtime irrelevant: this proof will erase at runtime
>   let 0 step1 : (reverse xs ++ [x] = reverse (x :: xs))
>               = revAppend [x] xs
>       step2 : x `Elem` [x] = Here
>       step3 : x `Elem` reverse xs ++ [x]
>             = elemAppRight (reverse xs) [x] step2
>      -- v-- look at `:t replace`
>   in replace {p = (x `Elem`)} step1 step3

> elemInReverse (y :: xs) (There p) =
>   let 0 step1 : (reverse xs ++ [y] = reverse (y :: xs))
>             = revAppend [y] xs
>       step2 : x `Elem` (reverse xs) = elemInReverse xs p
>       step3 : x `Elem` reverse xs ++ [y]
>             = elemAppLeft (reverse xs) [y] step2
>   in replace {p = (x `Elem`)} step1 step3

For steps 1,3, we used library functions that 'do the right
thing'. Since Idris2 is so young, we're not always so lucky and we
might need to prove our own results. If they're general enough, we can
submit a PR to the standard library, as we plan to do here.

Step 2 is left as an exercise:
[X] 2. You fill in the hole `Exercise2`.

Finally, we put steps 1,3 together using the `replace` function.

Let's spend some time looking at the equality type and the replace function.

  λΠ> :set showimplicits
  λΠ> :doc Equal
  Prelude.Equal : Prec


  Builtin.Equal : {0 a : Type} -> {0 b : Type} -> a -> b -> Type
    Totality: total
    Constructor: Refl : {0 a : Type} -> {0 x : a} -> Equal {a} {b = a} x x

  λΠ> :unset showimplicits

So `Equal` is indexed by 2 types, and two elements of each type. It
has a single constructor: `Refl {x} : x `Equal` x`.

Idris has 3 syntaxes that expand to Equal:

`x === y`: expands to `Equals {a} {b = a} x y` ('homogeneous equality')
`x ~=~ y`: expands to `Equals {a} {b}     x y` ('heterogeneous equality')
`x  =  y`: tries to expand to `x === y`, but if that doesn't work out, will expand to `x ~=~ y.
                                   ('best effort equality', non-standard personal terminology)

We can talk _a lot_ about equality, but we'll do that on a different
day.

Next, let's look at `replace` (I renamed the arguments a little bit):

  λΠ> :printdef replace
  Builtin.replace : {0 p : a -> Type} -> (0 prf : x = y) -> p x -> p y
  replace Refl i = i

It looks like `replace` doesn't do much - and that's the point! We're
convincing the type-checker that two terms it thinks are different are
going to be the same at runtime.

[X] 3. Implement your own version of `replace` interactively:

a. Declare `replace' : {0 p : a -> Type} -> (0 prf : x = y) -> p x -> p y
b. Generate a definition for `replace'`. What does the hole say?
c. Case split on the `prf` argument. What does the hole say now? What changed?
d. Fill the hole.

> replace' : {0 p : a -> Type} -> (0 prf : x = y) -> p x -> p y
> replace' Refl z = z
## Inductive step

[X] 4. Now you try! You can use the same structure as before.

 0 a : Type
 0 x : a
   y : a
   xs : List a
   i : Elem x xs
------------------------------
elemInReverse_rhs_2 : Elem x (reverseOnto [y] xs)

[X] 5. Can we make `xs` runtime irrelevant?

Hint: V qba'g guvax fb. Jul?

As always, once we implement the program, we step back and refactor.
Whether or not we can make `xs` irrelevant, lets try an implementation
that splits on `xs` first:

> total
> elemInReverse' : (xs : List a) -> (pos : x `Elem` xs) -> x `Elem` (reverse xs)

> elemInReverse' (y :: xs) pos =
>   let 0 eqPrf : (reverse xs ++ [y] = reverse (y :: xs))
>             = revAppend [y] xs
>       rev : x `Elem` reverse xs ++ [y]
>           = case pos of
>                 Here => elemAppRight (reverse xs) [x] Here
>                 (There p) => elemAppLeft (reverse xs) [y] $ elemInReverse' xs p
>   in replace {p = (x `Elem`)} eqPrf rev

Notice that the case `xs = Nil` is impossible: we didn't need to
consider it at all so far! If we just delete it, Idris can still work
out that no possible cases are missing. The part of Idris that checks
that is called the _coverage checker_.

[X] 6. Refactor your definition above into `elemInReverse'`


## Inspecting case trees

We can see what Idris compiled `elemInReverse` into using the REPL
command `:di`, which stands for *d*ebug *i*nformation:

:di elemInReverse
... lots of stuff ...
Compiled:
 0   [{arg:2}, {arg:3}]:
 1     (%case !{arg:2}
 2       [(%concase [cons] Prelude.Basics.:: Just 1 [{e:1}, {e:2}]
 3         (%case !{arg:3}
 4           [(%concase [nothing] Data.List.Elem.Here Just 0 []
 5              (%let step2 (((((Sheets.FP.Exercise2 []) [___]) [___]) [___]) [___])
 6              (%let step3 (Data.List.Elem.Extra.elemAppRight
 7                            [ (Data.List.reverse [!{e:2}])
 8                            , (%con [cons] Prelude.Basics.:: Just 1
 9                               [!{e:1}, (%con [nil] Prelude.Basics.Nil Just 0 [])])
10                            , !step2])
11                            !step3)))
12           , (%concase [just] Data.List.Elem.There Just 1 [{e:10}]
13                (%let step2 (Sheets.FP.elemInReverse [!{e:2}, !{e:10}])
14                (%let step3 (Data.List.Elem.Extra.elemAppLeft
15                              [ (Data.List.reverseOnto [(%con [nil] Prelude.Basics.Nil Just 0 [])
16                                                       , !{e:2}])
17                              , (%con [cons] Prelude.Basics.::
18                                               Just 1
19                                               [ !{e:1}
20                                               , (%con [nil] Prelude.Basics.Nil Just 0 [])
21                                               ])
22                              , !step2
23                              ])
24                            !step3)))
25           ]
26           Nothing))
27       ] Nothing)
... more stuff ...

I re-indended it, since the output is unreadable without
reformatting. Despite the reformatting, this is quite horrible, but
it's still interesting to try and see what's happening despite all the
noise.

+ Line 0: we see that the function has two runtime arguments `{arg:2}`
and `{arg:3}`.  That's because `elemInReverse` has to _implict_,
runtime irrelevant arguments:

 < elemInReverse : {0 a : Type} -> {0 x : a} ->     -- Implicit arguments!
 <   (xs : List a) -> (pos : x `Elem` xs) -> x `Elem` (reverse xs)

Whenever idris encounters a lowercase identifier in a type
declaration, it adds it to the list of implicitly bound
runtime-irrelevant variables at the beginning of the type
declaration. This can sometimes lead to unexpected behaviour, and
we'll probably run into it this summer and then I'll explain it in
more detail.

+ Line 1: we start by case-splitting on `{arg:2}`, that is `xs`.  We
have a single case at runtime, we never need to deal with the case `xs
= Nil`, and the compiled code won't check this possibility.

+ Line 2 is the shared case `x :: xs`/`y :: xs`, and `e:1` is `x` in
the first case (with `Here`) and `e:1` is `y` in the second case (with
`There i`).

+ Line 3 splits on the second argument `{arg:3}`, the position.

+ Line 4 is the case where the position is `Here`.

+ As you can see, line 5 jumps directly to `step2`: `step1` does not
appear in the compiled code at all!

+ Similarly, the `replace` function has also been completely erased:
line 11 simply returns `step3`.


[X] 7. a. In which lines do we see the compiled code for `[x]` and `[y]`?
       b. Repeat this analysis for the refactored version from exercise 6.


Now let's apply all you've learned in our new `Data.SnocList.Elem` library:

[X] 8. Implement a `SnocList` analogue to `thereInjectiv`.


# Impossible cases

In the previous section, we saw that the coverage checker can
sometimes notice that some cases are impossible. However, checking for
impossible cases is undecidable, and so the coverage checker is
guaranteed to fail to notice an impossiblity when your case splitting
becomes complicated enough.

Like the previous section, this has several moving parts, and we can
spend a lot of time on it. We will just cover the ones we need for our
`Data.SnocList.Element` module.

  λΠ> :doc Void
  Builtin.Void : Type
    The empty type, also known as the trivially false proposition.

    Use `void` or `absurd` to prove anything if you have a variable of type
    `Void` in scope.
    Totality: total

`Void` has no constructors. So if we manage to get a value of type
`Void`, we can case-split on it and return any value using the stdlib
function `void`.  Let's implement it ourselves:

> void' : Void -> a
> void' bottom = case bottom of {}

Aside on syntax: in Idris, you can use braces and semicolons instead of indented blocks, so:
 < case boolean of {True => ?trueCase; False => ?falseCase}
is a 1 line
 < case boolean of
 <   True  => ?trueCase
 <   False => ?falseCase

So the definition of `void'` is a case-split with no cases.

Two other ways to implement it:

> void'' : Void -> a
> void'' bottom impossible

> covering
> void''' : Bool -> a

Going all the way to `Void` leads to low-level programs, and the
stdlib has an interface that helps us write higher-level programs:

  λΠ> :doc Uninhabited
  Prelude.Uninhabited : Type -> Type
    A canonical proof that some type is empty.
    Parameters: t
    Methods:
      uninhabited : t -> Void
        If I have a t, I've had a contradiction.
        @ t the uninhabited type
    Implementations:
      Uninhabited (Here = There e)
      Uninhabited (There e = Here)
      Uninhabited (Elem x [])
      ... and so on ...

So an uninhabited type is one from which we can produve a `Void`.

[ ] 1. Implement `SnocList` analogues to:

 < Uninhabited (Here = There e)
 < Uninhabited (There e = Here)
 < Uninhabited (Elem {a} x [<])


Uninhabited types, types whose values let us construct a `Void`, are
useful for pruning impossible cases. So it's useful to be able to
package these types in a type:

  λΠ> :printdef Not
  Prelude.Not : Type -> Type
  Not x = x -> Void


[ ] 2. Implement the `SnocList` analogue to `neitherHereNorThere`.

# Decidable types

The last topic we're going to cover!

  λΠ> :doc Dec
  Prelude.Dec : Type -> Type
    Decidability. A decidable property either holds or is a contradiction.
    Totality: total
    Constructors:
      Yes : prop -> Dec prop
        The case where the property holds.
        @ prf the proof
      No : (prop -> Void) -> Dec prop
        The case where the property holding would be a contradiction.
        @ contra a demonstration that prop would be a contradiction


`Dec p` is a pre-packaged version of `Either p (Not p)`, with `Yes` a
more informative label than `Left` and `No` more informative than
`Right`.

A special case of it is the decidable equality interface:


  λΠ> :doc DecEq
  Decidable.Equality.DecEq : Type -> Type
    Decision procedures for propositional equality
    Parameters: t
    Methods:
      decEq : (x1 : t) -> (x2 : t) -> Dec (x1 = x2)
        Decide whether two elements of `t` are propositionally equal
    Implementations:
      DecEq (Elem x xs)
      ... and many others ...


[ ] 3. Implement a `DecEq (x `Elem` xs)` for SnocLists.

  You'll need a _view_ for the case `decEq (There this) (There
  this)`. This is the `with` keyword, and it does two things:

  a. It adds another column to a block of function-definition patterns.

  b. For each case in that block, it will find occurrences of the
     argument to `with` in the current context, and replace them with
     current pattern.

  Behaviour b can be a bit abstract, so we'll come back to it at a
  later sheet. But it's good to know that `with` has this behaviour
  from the very beginning!


If you haven't already, please show your solutions to Ohad :).

# Putting it all together

[ ] 1. Prepare a PR for your new `Data.SnocList.Element` module

a. Find where to put it in the Idris project.
b. Update the appropriate .ipkg file.
c. Make sure it compiles.
d. Create a _draft_ PR.
