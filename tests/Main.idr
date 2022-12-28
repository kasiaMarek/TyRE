module Main

import Test.Golden

%default covering

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
              "tyre/appointment",
              "tyre/time-full"
            ]

disjointMatches : TestPool
disjointMatches = MkTestPool "disjointmatches" [] Nothing
                    [
                      "disjointmatches/ex01"
                    ]

main : IO ()
main = runner [ stringTests, tyre, disjointMatches]
