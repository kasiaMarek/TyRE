import Data.Regex

re : TyRE (Maybe Nat)
re = r "((a*d)|(bb))!"

dm : DisjointMatches (Maybe Nat)
dm = asDisjointMatches re "ghaadfafaadbbbbbhaaaaaadf"

main : IO ()
main = do printLn $ asDisjointMatches re "aaadeebbjk"
          printLn $ dm
          printLn $ (Prefix [<]) <>< dm