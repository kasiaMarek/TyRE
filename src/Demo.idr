import Data.Regex
import TyRE.NFA.PrettyPrint
import TyRE.Thompson.GroupThompson
import TyRE.NFA

main : IO ()
main = do putStrLn $ show $ parse (compile $ Rep1 (To 'a' 'z')) "a"
          putStrLn $ show $ parse (compile $ To 'a' 'z') "a"
          putStrLn $ show $ parse (compile $ Rep0 (To 'a' 'z')) "a"
          putStrLn $ show $ parse (ignore $ rep1 $ r "[a-z]") "a"
          putStrLn $ show $ parse (ignore $ r "ab") "ab"

Ordered Char where
  all = ['a','b','c','d']

Ordered (Maybe Nat) where
  all = [Just 0, Just 1, Just 2, Just 3, Just 4, Just 5, Just 6, Just 7, Just 8, Just 9, Just 10, Nothing]

re : CoreRE
re = compile (r "[a-c]+")

p : IO ()
p = do putStrLn $ printNFA (smToNFA $ groupThompson re)
       putStrLn $ printNFA (smToNFA $ groupThompsonNoMin re)

mappings : IO ()
mappings = putStrLn $ show $ printFstMappings re

printPostSquash : IO ()
printPostSquash = putStrLn $ show $ postSquash re