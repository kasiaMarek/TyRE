module Core

import public Codes

%default total

public export
data CoreRE =
    Pred (Char -> Bool)
    | Concat CoreRE CoreRE
    | Group CoreRE
    | Empty
    | Alt CoreRE CoreRE
    -- | Star CoreRE

public export
ShapeCode: CoreRE -> Code
ShapeCode (Pred f)      = CharC
ShapeCode (Concat x y)  = PairC (ShapeCode x) (ShapeCode y)
ShapeCode (Group _)     = StringC
ShapeCode Empty         = UnitC
ShapeCode (Alt x y)     = EitherC (ShapeCode x) (ShapeCode y)
-- ShapeCode (Star x)      = ListC (ShapeCode x)

public export
Shape: CoreRE -> Type
Shape = Sem . ShapeCode

public export
ShapeSimp: CoreRE -> Type
ShapeSimp = Sem . SimplifyCode . ShapeCode

public export
showAux : {re : CoreRE} -> Shape re -> String
showAux {re = (Pred _)} c = show c
showAux {re = (Concat re1 re2)} (sh1, sh2) = "(" ++ showAux sh1 ++ ", " ++ showAux sh2 ++ ")"
showAux {re = (Group _)} str = str
showAux {re = (Alt re1 re2)} (Left x) = "Left " ++ showAux x
showAux {re = (Alt re1 re2)} (Right x) = "Right " ++ showAux x
showAux {re = Empty} () = "()"
