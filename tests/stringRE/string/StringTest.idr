module StringTest

import StringRE

printParsed : String -> IO ()
printParsed str = case (r str) of
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
