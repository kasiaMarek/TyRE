module CommonRegexes.DateAndTime

import API
import StringRE

public export
record Date where
    constructor D
    year : Integer
    month : Integer
    day : Integer

public export
Show Date where
    show (D y m d) = show y ++ "-" ++ show m ++ "-" ++ show d

public export
record Time where
    constructor T
    hours : Integer
    min : Integer
    sec : Integer
    milis : Integer

public export
Show Time where
    show (T h m s ms) = show h ++ ":" ++ show m ++ ":" ++ show s ++ "." ++ show ms

public export
record DateTime where
    constructor DT
    date : Date
    time : Time

public export
Show DateTime where
    show (DT d t) = show d ++ "T" ++ show t

int : Char -> Integer
int c = cast c - cast '0'

hourConv : Either (Char, Char) Char -> Integer
hourConv (Left (t, d)) = 10 * int t + int d
hourConv (Right d) = 20 + int d

yearConv : (Integer, Integer, Integer, Integer) -> Integer
yearConv (th, h, t, d) = 1000 * th + 100 * h + 10 * t + d

dayConv : Either (Bool, Char) (Char, Char) -> Integer
dayConv (Left (_, d)) = int d
dayConv (Right (t, d)) = 10 * int t + int d

monthConv : Either (Bool, Char) Char -> Integer
monthConv (Left (_, c)) = int c
monthConv (Right c) = 10 + int c

||| hour regex
hour : TyRE Integer 
hour = hourConv `Conv` r "([01][0-9])|(2[0-4])"

||| minutes or seconds regex
mOrS : TyRE Integer 
mOrS = (\case(t, d) => 10 * int t + int d) `Conv` r ":[0-5][0-9]"

milis : TyRE Integer
milis = (\case (h, t, d) => 100 * h + 10 * t + d) `Conv` match '.' *> digit <*> (digit <*> digit)

||| year regex
year : TyRE Integer
year = yearConv `Conv` repTimes 4 digit

||| day regex from 01 to 20
day : TyRE Integer
day = dayConv `Conv` r "(0?[1-9])|([12][0-9])"

||| month regex
month : TyRE Integer
month = monthConv `Conv` r "(0?[1-9])|(1[0-2])"

||| Date regex pattern: DD/MM/YYYY (24.03.1999)
export
date : TyRE Date
date = 
    let thirtieth := Conv   ((withSnd 30) . monthConv)
                            (r "30/((0?[13456789])|(1[012]))")
        thirtyfirst := Conv ((withSnd 31) . monthConv)
                            (r "31/((0?[13578])|(1[02]))")
    in Conv (\case ((d, m), y) => D y m d) $ 
            ((((day <* match '/') <*> month) `or` thirtieth) `or` thirtyfirst) 
                <*> (match '/' *> year) where
    withSnd : Integer -> (Integer -> (Integer, Integer))
    withSnd fst snd = (fst, snd)

||| Time regex pattern: 
|||     HH:mm (22:53)
|||     HH:mm:ss (22:53:34)
export
time : TyRE Time
time = conv `Conv` hour <*> (mOrS <*> option mOrS) where
    conv : (Integer, Integer, Maybe Integer) -> Time
    conv (h, m, Just s) = T h m s 0
    conv (h, m, Nothing) = T h m 0 0

||| ISO date
||| supported patterns:
|||     YYYY-MM-DD (1999-03-24)
|||     YYYY-MM-DDTHH:mm (1999-03-24T22:53)
|||     YYYY-MM-DDTHH:mm:ss (1999-03-24T22:53:34)
|||     YYYY-MM-DDTHH:mm:ss.sss (1999-03-24T22:53:34.011)
|||     YYYY-MM-DDTHH:mm:ss.sss(+-)HH:mm (1999-03-24T22:53:34.011+01:00)
export
iso : TyRE DateTime
iso =
    let thirtieth := ((withFst 30) . monthConv) `Conv` r "((0?[13456789])|(1[012]))\\-30"
        thirtyfirst := ((withFst 31) . monthConv) `Conv` r "((0?[13578])|(1[02]))\\-31"
        date := Conv (\case (y, m, d) => D y m d) $
                    (year <* match '-') <*> 
                    ((((month <* match '-') <*> day) `or` thirtieth) `or` thirtyfirst)
        time := convTime `Conv` hour <*> (mOrS <*> option (mOrS <*> option milis))
        timeZone := match 'Z' <|> ((match '+' <|> match '-') <*> (hour <*> mOrS))
    in conv `Conv` (date <*> option (convTimeWithZone `Conv` (match 'T' *> time <*> option timeZone))) where
        withFst : Integer -> (Integer -> (Integer, Integer))
        withFst snd fst = (fst, snd)

        convTime : (Integer, Integer, Maybe (Integer, Maybe Integer)) -> Time
        convTime (h, m, Just (s, Just ms)) = T h m s ms
        convTime (h, m, Just (s, _)) = T h m s 0
        convTime (h, m, _) = T h m 0 0

        convTimeWithZone : (Time, Maybe (Either () ((Either () ()), Integer, Integer))) -> (Time, Maybe Bool)
        convTimeWithZone (T hr min sec milis, Just (Right (Right _, h, m))) =
            let totMin := min + m
                (minutes, plusHour) := if totMin > 59 then (totMin - 60, 1) else (totMin, 0)
                totHr := hr + h + plusHour
                (hours, plusDay) := if totHr > 23 then (totHr - 24, Just True) else (totHr, Nothing)
            in (T hours minutes sec milis, plusDay)
        convTimeWithZone (T hr min sec milis, Just (Right (Left _, h, m))) =
            let totMin := min - m
                (minutes, minHour) := if totMin < 0 then (totMin + 60, 1) else (totMin, 0)
                totHr := hr - h - minHour
                (hours, minDay) := if totHr < 0 then (totHr + 24, Just False) else (totHr, Nothing)
            in (T hours minutes sec milis, minDay)
        convTimeWithZone (time, _) = (time, Nothing)

        conv : (Date, Maybe (Time, Maybe Bool)) -> DateTime
        conv (D y m d, Just (time, Just True)) = 
            let date :=
                if      (d == 30 && (m == 4 || m == 6 || m == 9 || m == 11)) 
                    ||  (d == 31 && (m == 1 || m == 3 || m == 5 || m == 7 || m == 8 || m == 10))
                    ||  (m == 2 && 
                        (   (d == 29 && mod y 4 == 0 && mod y 100 /= 0) 
                        ||  (d == 28 && (mod y 4 /= 0 || mod y 100 == 0)))) 
                    then D 1 (m + 1) y 
                    else if (d == 31 && m == 12) then D 1 1 (y + 1) else D (d + 1) m y
            in DT date time
        conv (D y m d, Just (time, Just False)) = 
            let date := 
                    if d == 1 
                        then if m == 1 then D (y - 1) 12 31
                            else 
                                if (m == 5 || m == 7 || m == 10 || m == 12) 
                                    then D y (m - 1) 31
                                    else
                                        if (m == 2 || m == 4 || m == 6 || m == 8 || m == 9 || m == 11)
                                            then D y (m - 1) 30
                                            else
                                                if (mod y 4 == 0 && mod y 100 /= 0)
                                                    then D y (m - 1) 29
                                                    else D y (m - 1) 28
                        else D y m (d - 1)
            in DT date time

        conv (date, Just (time, _)) = DT date time
        conv (date, _) = DT date (T 0 0 0 0)