# TyRE

Dependently-typed regex parser in Idris 2.

We assign each regex pattern a _shape_ which denotes the type of the of the output parse tree, e.g. `"[a-c]*"` has type `List Char`. We guarantee result type correctness with dependent-type verification. On top of the parser we add [Radanne's](https://doi.org/10.1145/3294032.3294082) type-indexed combinators (_tyre_).

### Usage
To use TyRE add needed dependencies to your .ipkg file. (_Please note: the order of dependencies matters - `contrib` needs to be after `tyre`._)
```
depends = tyre, contrib
```
Now just import `Data.Regex`, which cointains the following functions for parsing and matching:
```Idris
getToken : TyRE a -> Stream Char -> (Maybe a, Stream Char)
match : TyRE a -> String -> Bool
parse : TyRE a -> String -> Maybe a
```
#### Example
Parsing time (from `tests/tyre/time-full`):
```Idris
import Data.Regex

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
