import TyRE.StringRE

printParsed : String -> IO ()
printParsed str = case (rAux str) of
                    (Just result) => putStrLn $ show result
                    Nothing => putStrLn $ str ++ " does not parse"

main : IO ()
main = do printParsed "ab"
          printParsed "\\-"
          printParsed "d[a-z]"
          printParsed "[nhj]"
          printParsed "d[nhj\\-]o"
          printParsed "`kl[0-9]`df"
          printParsed "(`kl[0-9]`d)fhh"
          printParsed "((`kl([0-9]nn)k[jkl]`d)fh)h"
          printParsed "((`kl([0-9]nn)(k[jkl])`d)fh)(h)"
          printParsed "((`kl([0-9][\\`]nn)(k[jkl])`d)fh)(h)"
          printParsed "a|b"
          printParsed "(a|b)m"
          printParsed "([0-9]*)oi(ss)|m"
          printParsed "uuu(u+)?"
          printParsed "ab?c"
