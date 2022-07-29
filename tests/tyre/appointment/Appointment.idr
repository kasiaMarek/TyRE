import Data.Regex

data WeekDay = Mon | Tue | Wed | Thu | Fri

Show WeekDay where
  show Mon = "1"
  show Tue = "2"
  show Wed = "3"
  show Thu = "4"
  show Fri = "5"

aday : TyRE () -> WeekDay -> TyRE WeekDay
aday tyre wday = (\_ => wday)`map` tyre

day : TyRE WeekDay
day =       (aday (r "Mon") Mon)
    `or`  ( (aday (r "Tue") Tue)
    `or`  ( (aday (r "Wed") Wed)
    `or`  ( (aday (r "Thu") Thu)
    `or`    (aday (r "Fri") Fri) )))

hour : TyRE Integer
hour =
  let toInt : Char -> Integer
      toInt c = 10 + cast c - cast '0'
      adjustAmOrPm : (Integer, Bool) -> Integer
      adjustAmOrPm (i, True) = i
      adjustAmOrPm (i, False) = 12 + i
  in adjustAmOrPm `map`
            ((option (match '0') *> digit) `or` (toInt `map` r "1[0-2]!"))
        <*> r "((am)|(pm))!"

appointment : TyRE (WeekDay, Integer)
appointment =  day <* match ' ' <*> hour

main : IO ()
main = do putStrLn $ show $ parse appointment "Mon 9am"
          putStrLn $ show $ parse appointment "Tue 03am"
          putStrLn $ show $ parse appointment "Fri 11am"
          putStrLn $ show $ parse appointment "Fri11am"
          putStrLn $ show $ parse appointment "Fri 13am"
