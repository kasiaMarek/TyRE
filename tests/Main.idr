module Main

import Test.Golden

%default covering

fullTests : TestPool
fullTests = MkTestPool "fulltests" [] [ "fulltests/time"]

main : IO ()
main = runner [ fullTests ]
