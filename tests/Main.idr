module Main

import Test.Golden

%default covering

nfa : TestPool
nfa = MkTestPool "nfa" [] Nothing
      [ "nfa/even",
        "nfa/empty",
        "nfa/foo"
      ]

fullTests : TestPool
fullTests = MkTestPool "fulltests" [] Nothing
            [ "fulltests/time",
              "fulltests/foo",
              "fulltests/ab"
            ]

stringTests : TestPool
stringTests = MkTestPool "stringRE" [] Nothing
            [ "stringRE/string",
              "stringRE/full"
            ]

fullTyRETests : TestPool
fullTyRETests = MkTestPool "fulltyre" [] Nothing
            [ "fulltyre/time",
              "fulltyre/timeNoStr"
            ]

main : IO ()
main = runner [ nfa, fullTests, stringTests, fullTyRETests ]
