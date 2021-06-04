module Core
%default total

public export
data CoreRE =
    Pred (Char -> Bool)
    | Concat CoreRE CoreRE
    | Group CoreRE
    -- | Empty
    -- | Alt CoreRE CoreRE
    -- | Star CoreRE
