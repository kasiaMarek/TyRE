module StringRE

import Core
import Data.List
import public Text.Lexer
import public Text.Parser
import public Data.Maybe

public export
data RE =
    Exactly Char
  | OneOf (List Char)
  | To Char Char
  | Concat RE RE
  | Group RE

public export
Eq RE where
  (Exactly x) == (Exactly x')                 = x == x'
  (OneOf xs) == (OneOf ys)                    = xs == ys
  (x `To` y) == (x' `To` y')                  = (x == x') && (y == y')
  (re1 `Concat` re2) == (re1' `Concat` re2')  = (re1 == re1') && (re2 == re2')
  (Group x) == (Group x')                     = x == x'
  _ == _                                      = False


public export
compile               : RE -> CoreRE
compile (Exactly x)   = Pred (\e => e == x)
compile (OneOf xs)    = Pred (\e => case (find (\x => e == x) xs) of {(Just _) => True ; Nothing => False})
compile (To x y)      = Pred (\c =>  x <= c && c <= y)
compile (Concat x y)  = Concat (compile x) (compile y)
compile (Group x)     = Group (compile x)

public export
specialChars : String
specialChars = "[]()\\`-"

public export
mapChar : Char -> String
mapChar c = case (find (\sc => c == sc) (unpack specialChars)) of {Just _ => "\\" ++ (cast c); Nothing => (cast c)}

public export
Show RE where
  show (Exactly c) = mapChar c
  show (OneOf xs) = "[" ++ (foldl (++) "" (map mapChar xs)) ++ "]"
  show (x `To` y) = "[" ++ (mapChar x) ++ "-" ++ (mapChar y) ++ "]"
  show (Concat (Concat x z) y) = "(" ++ (show (Concat x z)) ++ ")" ++ (show y)
  show (Concat atomX y) = show atomX ++ show y
  show (Group x) = "`" ++ show x ++ "`"

public export
data Token =
              OParQ
            | CParQ
            | OPar
            | CPar
            | BackTic
            | Dash
            | CharLit String

public export
reCharLit : Lexer
reCharLit = (non $ some $ oneOf specialChars) <|> (is '\\' <+> any)

public export
reTokenMap : TokenMap Token
reTokenMap = [
              (reCharLit, \x => CharLit x),
              (is '[',    \x => OParQ),
              (is ']',    \x => CParQ),
              (is '(',    \x => OPar),
              (is ')',    \x => CPar),
              (is '`',    \x => BackTic),
              (is '-',    \x => Dash)
              ]

public export
Rule : Type -> Type
Rule ty = Grammar (TokenData Token) True ty

public export
getCharLit : (TokenData Token) -> Maybe Char
getCharLit (MkToken _ _ (CharLit str)) with (unpack str)
  getCharLit (MkToken _ _ (CharLit str)) | [] = Nothing --should not happen
  getCharLit (MkToken _ _ (CharLit str)) | (c :: []) = Just c
  getCharLit (MkToken _ _ (CharLit str)) | ('\\' :: (c :: [])) = Just c
  getCharLit (MkToken _ _ (CharLit str)) | ('\\' :: (c :: (c' :: cs))) = Nothing --should not happen
  getCharLit (MkToken _ _ (CharLit str)) | (c :: (c' :: cs)) = Nothing --should not happen
getCharLit _ = Nothing

public export
charLit : Rule Char
charLit = terminal "char" getCharLit

public export
getTerminalRule : String -> (Token -> Bool) -> Rule ()
getTerminalRule str pred = terminal str (\(MkToken _ _ tok) => if (pred tok) then Just () else Nothing)

public export
openParQ : Rule ()
openParQ = getTerminalRule "[" \case {OParQ => True; _ => False}

public export
closedParQ : Rule ()
closedParQ = getTerminalRule "]" \case {CParQ => True; _ => False}

public export
openPar : Rule ()
openPar = getTerminalRule "(" \case {OPar => True; _ => False}

public export
closedPar : Rule ()
closedPar = getTerminalRule ")" \case {CPar => True; _ => False}

public export
backTic : Rule ()
backTic = getTerminalRule "`" \case {BackTic => True; _ => False}

public export
dash : Rule ()
dash = getTerminalRule "-" \case {Dash => True; _ => False}

public export
charLitsRep : Rule (List Char)
charLitsRep = (map (::) charLit <*> charLitsRep) <|> (map (\x => [x]) charLit)

public export
fromTo : Rule RE
fromTo = (map To ((openParQ *> charLit) <* dash) <*> charLit) <* closedParQ

public export
oneOf : Rule RE
oneOf = map OneOf $ openParQ *> charLitsRep <* closedParQ

public export
exactly : Rule RE
exactly = map Exactly charLit

public export
atomREnoGroup : Rule RE
atomREnoGroup = fromTo <|> oneOf <|> exactly

public export
reNoGroup : Rule RE
reNoGroup =   (map Concat atomREnoGroup                       <*> reNoGroup)
          <|> (map Concat atomREnoGroup                       <*> (openPar *> reNoGroup <* closedPar))
          <|> (map Concat (openPar *> reNoGroup <* closedPar) <*> reNoGroup)
          <|> (map Concat (openPar *> reNoGroup <* closedPar) <*> (openPar *> reNoGroup <* closedPar))
          <|> atomREnoGroup
          <|> (openPar *> atomREnoGroup <* closedPar)

public export
group : Rule RE
group = map Group (backTic *> reNoGroup <* backTic)

public export
atomRE : Rule RE
atomRE = group <|> atomREnoGroup

public export
reRule : Rule RE
reRule =
      (map Concat atomRE                            <*> reRule)
  <|> (map Concat atomRE                            <*> (openPar *> reRule <* closedPar))
  <|> (map Concat (openPar *> reRule <* closedPar)  <*> reNoGroup)
  <|> (map Concat (openPar *> reRule <* closedPar)  <*> (openPar *> reRule <* closedPar))
  <|> atomRE
  <|> (openPar *> atomRE <* closedPar)

public export
rAux : String -> Maybe RE
rAux str = case (parse reRule (fst (lex reTokenMap str))) of
                    Right (reg, _) => Just reg
                    Left _ => Nothing

public export
r : (str: String) -> {auto isJust : IsJust (rAux str)} -> RE
r str {isJust} = fromJust (rAux str) @{isJust}
