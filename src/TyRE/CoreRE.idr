module TyRE.CoreRE

import Data.SortedSet
import Data.List

import public TyRE.Codes

%default total

public export 
data CharCond =
      OneOf (SortedSet Char)
    | Range (Char, Char)
    | Pred (Char -> Bool)

public export
Eq CharCond where
  (==) (OneOf x) (OneOf y) = x == y
  (==) (OneOf x) _ = False
  (==) (Range x) (Range y) = x == y
  (==) (Range x) _ = False
  (==) (Pred _) _ = False

public export
data CoreRE =
      CharPred CharCond
    | Concat CoreRE CoreRE
    | Group CoreRE
    | Empty
    | Alt CoreRE CoreRE
    | Star CoreRE

public export
satisfies : CharCond -> Char -> Bool
satisfies (OneOf xs) c = contains c xs
satisfies (Range (x, y)) c = x <= c && c <= y
satisfies (Pred f) c = f c

public export
ShapeCode : CoreRE -> Code
ShapeCode (CharPred _)  = CharC
ShapeCode (Concat x y)  = PairC (ShapeCode x) (ShapeCode y)
ShapeCode (Group _)     = StringC
ShapeCode Empty         = UnitC
ShapeCode (Alt x y)     = EitherC (ShapeCode x) (ShapeCode y)
ShapeCode (Star x)      = ListC (ShapeCode x)

public export
Shape : CoreRE -> Type
Shape = Sem . ShapeCode

public export
ShapeSimp : CoreRE -> Type
ShapeSimp = Sem . SimplifyCode . ShapeCode

public export
showAux : {re : CoreRE} -> Shape re -> String
showAux {re = (CharPred _)} c = show c
showAux {re = (Concat re1 re2)} (sh1, sh2) = "(" ++ showAux sh1 ++ ", " ++ showAux sh2 ++ ")"
showAux {re = (Group _)} str = str
showAux {re = (Alt re1 re2)} (Left x) = "Left " ++ showAux x
showAux {re = (Alt re1 re2)} (Right x) = "Right " ++ showAux x
showAux {re = Empty} () = "()"
showAux {re = (Star re)} xs = show $ map (showAux {re}) xs
