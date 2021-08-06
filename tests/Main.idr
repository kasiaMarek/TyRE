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
corere = MkTestPool "core RE" [] Nothing
            [ "corere/time",
              "corere/foo",
              "corere/ab",
              "corere/star"
            ]

stringTests : TestPool
stringTests = MkTestPool "string syntax" [] Nothing
            [ "string-syntax/string",
              "string-syntax/full"
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
