# TyRE

Dependently-typed regex parser in Idris 2.

We assign each regex pattern a _shape_ which denotes the type of the of the output parse tree, e.g. `"[a-c]*"` has type `List Char`. We guarantee result type correctness with dependent-type verification. On top of the parser we add [Radanne's](https://doi.org/10.1145/3294032.3294082) type-indexed combinators (_tyre_).

#### Examples
Parsing time (from `tests/tyre/time-full`):
```Idris
digit : Char -> Integer
digit c = cast c - cast '0'

Time : TyRE (Integer, Integer)
Time = (f . fromEither `Conv` r "([01][0-9])|([2][0-4])")
        <*>  (f `Conv` r ":([0-5][0-9])") where
          f : (Char, Char) -> Integer
          f (x, y) = (10 * digit x + digit y)
```

#### Idris 2 Parser
The module `Text/*` is a copy of Idris 2 `Text/*` module from `contib` package with slight modifications -- dropped `PrettyPrint`, added `public export` annotations, `fastunpack` switched to `unpack`. We made this copy to Idris 2's type checker to fully reduce terms.

### Important
Current version works with my fork of Idris2: https://github.com/kasiaMarek/Idris2/tree/listProofs
