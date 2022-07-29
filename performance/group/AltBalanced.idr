import Data.Regex

altREType : Nat -> Type
altREType 0 = ()
altREType (S k) = Either (altREType k) (altREType k)

altRE : (n : Nat) -> TyRE (altREType n)
altRE 0 = match 'a'
altRE (S k) = altRE k <|> altRE k

getRE : Bool -> (n : Nat) -> TyRE (Either String (altREType n))
getRE True n = Left `map` group (altRE n)
getRE False n = Right `map` (altRE n)

toStr : (n : Nat) -> (altREType n) -> String
toStr 0 () = show ()
toStr (S k) (Left rest) = "Left " ++ (toStr k rest)
toStr (S k) (Right rest) = "Right " ++ (toStr k rest)

main : IO ()
main =  do  isGroup <- getLine
            str <- getLine
            if all isDigit (unpack str)
              then
                let n : Nat
                    n = (cast str)
                    re : TyRE (Either String (altREType n))
                    re = getRE (isGroup == "group") n
                in case parse re "a" of
                    Just (Right res) => putStrLn (toStr n res)
                    Just (Left res) => putStrLn res
                    Nothing => putStrLn "Error"
              else putStrLn "Second input should be a number"