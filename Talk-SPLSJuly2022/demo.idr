import Data.Regex
import Data.Regex.DateAndTime

import Data.Stream
import Data.List

-- room number
roomNumber : TyRE Char
roomNumber = r "A[0-9]"

parseRoomNumber : String -> IO ()
parseRoomNumber str = printLn (match roomNumber str)












-- tyre time
time' : TyRE (Integer, Integer)
time' = ?timeconv `Conv` r "(([01][0-9])|([2][0-4])):([0-5][0-9])"












-- tyre time
digit : Char -> Integer
digit c = cast c - cast '0'

time'' : TyRE (Integer, Integer)
time'' = 
  (f `Conv` (r "[01][0-9]"  `or` r "[2][0-4]"))
  <*>
  (f `Conv` r ":([0-5][0-9])") where
    f : (Char, Char) -> Integer
    f (c1, c2) = 10 * digit c1 + digit c2



parseTimeExample : IO ()
parseTimeExample = printLn (parse time'' "12:03")








---stream example
str : Stream Char
str = unfoldr mk (True, 0) where
  mk : (Bool, Integer) -> (Char, (Bool, Integer))
  mk (False, i) = (cast (i + cast '0'), (True, (i + 3) `mod` 10))
  mk (True, i) = ('A', (False, i))
--A0A3A6A9A2A5A8...

tokenSteam : Stream (Maybe Char)
tokenSteam = unfoldr (getToken roomNumber) str
-- Just 0, Just 3, ...


printStreamBeg : IO ()
printStreamBeg = printLn (pack (take 14 str) ++ "...")

printTokenStreamBeg : IO ()
printTokenStreamBeg = printLn (Prelude.take 7 tokenSteam)










---common regexes example
isoString : String
isoString = "1993-11-23T12:33:40+01:00"

isoTime : Maybe DateTime
isoTime = parse iso isoString

printTime : IO ()
printTime = 
  do  printLn isoTime
      printLn (map (.time.hours) isoTime)