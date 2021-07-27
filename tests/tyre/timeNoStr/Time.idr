import API
import RE

TimeRE: RE
TimeRE =
    (
        (
            (
                ('0' `To` '1')
                `Concat`
                ('0' `To` '9')
            )
            `Alt`
            (
                (Exactly '2')
                `Concat`
                ('1' `To` '4')
            )
        )
        `Concat`
        (Exactly ':')
    ) `Concat`
    (
        ('0' `To` '5')
        `Concat`
        ('0' `To` '9')
    )

toDig : Char -> Integer
toDig c = cast c - cast '0'

Time : TyRE (Integer, Integer)
Time = f `Conv` (compile TimeRE) where
  f : (Either (Char, Char) (Char), (Char, Char)) -> (Integer, Integer)
  f ((Left (h1,h2)), (m1,m2)) = (10 * toDig h1 + toDig h2, 10 * toDig m1 + toDig m2)
  f ((Right h2), (m1,m2)) = (20 + toDig h2, 10 * toDig m1 + toDig m2)

getTime : String -> Maybe (Integer, Integer)
getTime str = parse Time str

main : IO ()
main = do putStrLn $ show $ getTime "10:30"
          putStrLn $ show $ getTime "00:00"
          putStrLn $ show $ getTime "21:15"
