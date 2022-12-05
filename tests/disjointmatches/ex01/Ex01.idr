import Data.Regex
import TyRE.CoreRE
import TyRE.Core

re : TyRE (Maybe Nat)
re = r "((a*d)|(bb))!"

re2 : TyRE Nat
re2 = r "s(a*)!"

dm : DisjointMatches (Maybe Nat)
dm = asDisjointMatches re "ghaadfafaadbbbbbhaaaaaadf" True

main : IO ()
main = do printLn $ asDisjointMatches re  "aaadeebbjk"                True
          printLn $ asDisjointMatches re2 "saaadeebbjk"                True
          printLn $ asDisjointMatches re  "ghaadfafaadbbbbbhaaaaaadf" False
          printLn $ dm
          printLn $ (Prefix [<]) <>< dm