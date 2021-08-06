import API
import StringRE
import Data.Either

digit : Char -> Integer
digit c = cast c - cast '0'

Time : TyRE (Integer, Integer)
Time = (f . fromEither `Conv` r "([01][0-9])|([2][0-4])")
        <*>  (f `Conv` r ":([0-5][0-9])") where
          f : (Char, Char) -> Integer
          f (x, y) = (10 * digit x + digit y)

parseTime : String -> IO ()
parseTime str = printLn $ parse Time str

main : IO ()
main = do parseTime "20:30"
          parseTime "02:59"
          parseTime "02:60"
          parseTime "00:00"
          parseTime "11:23"
