module RE

import public Core
import public CoreTyRE
import Data.List

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
CodeShapeRE : RE -> Code
CodeShapeRE (Exactly _) = UnitC
CodeShapeRE (OneOf _) = CharC
CodeShapeRE (To _ _) = CharC
CodeShapeRE (Concat re1 re2) = PairC (CodeShapeRE re1) (CodeShapeRE re2)
CodeShapeRE (Group _) = StringC

public export
TypeRE : RE -> Type
TypeRE = (Sem . SimplifyCode . CodeShapeRE)

public export
pairEq : ((a, x) = (b, y)) -> (a = b, x = y)
pairEq Refl = (Refl, Refl)

mutual
  public export
  concatTyRE : (re1 : RE) -> (re2 : RE) -> CoreTyRE (TypeRE re1, TypeRE re2)
  concatTyRE re1 re2 = compile re1 <*> compile re2

  public export
  compile                  : (re : RE) -> CoreTyRE $ TypeRE re
  compile (Exactly x)      = (\x => ()) `Conv` Untyped (Pred (\e => e == x))
  compile (OneOf xs)       = Untyped $ Pred (\e => case (find (\x => e == x) xs) of {(Just _) => True ; Nothing => False})
  compile (To x y)         = Untyped $ Pred (\c =>  x <= c && c <= y)
  compile (Group re)       = Untyped $ Group $ compile $ compile re
  compile (Concat re1 re2) with (SimplifyCode (CodeShapeRE re1), SimplifyCode (CodeShapeRE re2)) proof p
    compile (Concat re1 re2) | (CharC, CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, (PairC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, UnitC) =
      let prf : (SimplifyCode (CodeShapeRE re1) = CharC)
          prf = fst $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(x, _) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), (PairC z w)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), UnitC) =
      let prf : (SimplifyCode (CodeShapeRE re1) = (PairC x y))
          prf = fst $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(x, _) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, (PairC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, UnitC) =
      let prf : (SimplifyCode (CodeShapeRE re1) = StringC)
          prf = fst $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(x, _) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | (UnitC, CharC) =
      let prf : (SimplifyCode (CodeShapeRE re2) = CharC)
          prf = snd $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(_,x) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | (UnitC, (PairC x y)) =
      let prf : (SimplifyCode (CodeShapeRE re2) = (PairC x y))
          prf = snd $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(_,x) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | (UnitC, StringC) =
      let prf : (SimplifyCode (CodeShapeRE re2) = StringC)
          prf = snd $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(_,x) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | (UnitC, UnitC) = (\x => ()) `Conv` concatTyRE re1 re2
