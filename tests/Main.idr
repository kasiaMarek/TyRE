module Main

import Test.Golden

%default covering

nfa : TestPool
nfa = MkTestPool "nfa" [] Nothing
      [ "nfa/even",
        "nfa/empty",
        "nfa/foo"
      ]

corere : TestPool
corere = MkTestPool "core re" [] Nothing
            [ "corere/time",
              "corere/foo",
              "corere/ab",
              "corere/star"
            ]

stringTests : TestPool
stringTests = MkTestPool "stringre" [] Nothing
            [ "stringre/string",
              "stringre/full"
            ]

tyre : TestPool
tyre = MkTestPool "tyre" [] Nothing
            [ "tyre/time",
              "tyre/timeNoStr",
              "tyre/tyre0",
              "tyre/appointment"
            ]

main : IO ()
main = runner [ nfa, corere, stringTests, tyre]
