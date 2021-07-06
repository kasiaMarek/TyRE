module Core

import public Codes

%default total

public export
data CoreRE =
    Pred (Char -> Bool)
    | Concat CoreRE CoreRE
    | Group CoreRE
    -- | Empty
    -- | Alt CoreRE CoreRE
    -- | Star CoreRE

public export
ShapeCode: CoreRE -> Code
ShapeCode (Pred f)      = CharC
ShapeCode (Concat x y)  = PairC (ShapeCode x) (ShapeCode y)
ShapeCode (Group _)     = StringC
-- ShapeCode Empty         = UnitC
-- ShapeCode (Alt x y)     = EitherC (ShapeCode x) (ShapeCode y)
-- ShapeCode (Star x)      = ListC (ShapeCode x)

public export
Shape: CoreRE -> Type
Shape = Sem . ShapeCode
