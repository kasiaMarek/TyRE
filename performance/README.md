### Performance tests.
We have the following performance tests:
  1. `./`: tests that compare the performance of tyre to Idris2 standard library parser combinators library for different regexes and words;
  2. `./group`: a test that compare the performance of:
     - a balanced alternation
     - an unbalanced alternation,
     - a balanced alternation wrapped in a `group` (`ignore`), and
     - an unbalanced alternation wrapped in a `group` (`ignore`).

#### Preconditions:
  1. `python` in version >= 3.4
  2. `matplotlib` module installed for python
  3. the `tyre` library version to be evaluated installed (can be done by running `make install` in the root directory)

#### Running the tests:
To run the tests run the following command in the chosen test directory:

`python3 runtests.py`

You may also wish to use one of the following flags when running the command:
  1. `--samples=${NUM_OF_SAMPLES}`
  2. `--idris2=${PATH_TO_IDRIS2}`

The created chart/s will be saved in `charts` directory.

#### Tests cases in `./`
All test are executed for n from 0 to 1000, each is sampled 5 times (this can be overwritten by the flag).
  1. Concatenation:
      - regex: "$a^n$"
      - parsee: "$a^n$"
      - tyre file: `ConcatTyRE.idr`
      - parsers combinations std lib file: `ConcatComb.idr`
  2. Alternation:
      - regex: "$a(|a)^n$"
      - parsee: "$a$"
      - tyre file: `AltTyRE.idr`
      - parsers combinations std lib file: `AltComb.idr`
  3. Simple Kleene star:
      - regex: "$a*$"
      - parsee: "$a^n$"
      - tyre file: `StarTyRE.idr`
      - parsers combinations std lib file: `StarComb.idr`
  4. Backtracking Kleene star:
      - regex: "$((a*c)\vert a)*b$"
      - parsee: "$a^nb$"
      - tyre file: `StarTyRE2.idr`
      - parsers combinations std lib file: `StarComb2.idr`