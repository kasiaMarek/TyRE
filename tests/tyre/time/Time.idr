import Data.Regex

toDig : Char -> Integer
toDig c = cast c - cast '0'

f : ((Char, Char), (Char, Char)) -> (Integer, Integer)
f ((h1,h2), (m1,m2)) = (10 * toDig h1 + toDig h2, 10 * toDig m1 + toDig m2)

Time : TyRE (Integer, Integer)
Time = f `map` r "([0-2][0-9])!:([0-5][0-9])!"

getTime : String -> Maybe (Integer, Integer)
getTime str = parse Time str

main : IO ()
main = do putStrLn $ show $ getTime "10:30"
          putStrLn $ show $ getTime "00:00"
