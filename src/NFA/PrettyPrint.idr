module NFA.PrettyPrint
import NFA
import Data.List
import Data.SnocList
import public NFA.PrettyPrint.Interfaces

transitionString : String -> String -> String -> String
transitionString from label to =
  from ++ " -> " ++ to ++ "[label = \"" ++ label ++ "\"];\n"

makeTransitionString : {auto nfa : NA} -> {auto s: Show nfa.State}
                -> nfa.State -> Char -> nfa.State -> String
makeTransitionString s c t = transitionString (show s) (cast c) (show t)
  --(show s) ++ " -> " ++ (show t) ++ "[label = \"" ++ cast c ++ "\"];\n"

nodeStyleString : String -> String -> String
nodeStyleString shape name =
  "node [shape = " ++ shape ++ "]; "
      ++ name ++ ";\n"

printNodeStyleString : {auto nfa : NA} -> {auto s: Show nfa.State}
                  -> nfa.State -> String
printNodeStyleString s =
  let circle : String
      circle = if (nfa.accepting s)
               then "doublecircle"
               else "circle"
  in nodeStyleString circle (show s)

record PrinterState (nfa : NA) where
  constructor MkPState
  seenStates : List (nfa .State)
  acc : SnocList String

printNodeStyle : {auto nfa : NA}
            -> {auto sh: Show nfa.State}
            -> nfa.State
            -> (PrinterState nfa)
            -> (PrinterState nfa)
printNodeStyle s (MkPState seenStates acc) =
  let _ := nfa.isEq
      currentAcc :=
        case find (== s) nfa.start of
          Nothing => acc :< (printNodeStyleString s)
          Just _ =>
            acc :< (nodeStyleString "point" ("St" ++ show s))
                :< (printNodeStyleString s)
                :< (transitionString ("St" ++ show s) "start" (show s))
  in MkPState (s::seenStates) currentAcc

printTransition : {auto nfa : NA}
                -> {auto sh: Show nfa.State}
                -> nfa.State
                -> Char -> nfa.State
                -> (PrinterState nfa) -> (PrinterState nfa)
printTransition s c t (MkPState seenStates acc) =
  MkPState seenStates (acc :< makeTransitionString s c t)

printTransitionsFrom : {auto nfa : NA}
                    -> {auto show: Show nfa.State}
                    -> nfa.State
                    -> Char -> List nfa.State
                    -> (PrinterState nfa) -> (PrinterState nfa)
printTransitionsFrom s c [] ps = ps
printTransitionsFrom s c (t :: ss) ps =
  let _ := nfa.isEq
      currPs := case find (==t) ps.seenStates of
                    Nothing => printNodeStyle t ps
                    (Just _) => ps
  in printTransitionsFrom s c ss (printTransition s c t currPs)

printTransitions : {auto nfa : NA} -> {auto show: Show nfa.State}  -> nfa.State
                -> List Char
                -> (PrinterState nfa) -> (PrinterState nfa)
printTransitions s [] ps = ps
printTransitions s (c :: cs) ps = printTransitionsFrom s c (nfa.next s c) ps

printState : {auto ord : Ordered Char}
          -> {auto nfa : NA}
          -> {auto show: Show nfa.State}
          -> nfa.State
          -> (PrinterState nfa)
          -> (PrinterState nfa)
printState x ps =
  let _ := nfa.isEq
  in case find (==x) ps.seenStates of
      Nothing => printTransitions x all (printNodeStyle x ps)
      (Just y) => printTransitions x all ps

printNFAFrom : {auto ord : Ordered Char}
            -> {auto nfa : NA}
            -> {auto show: Show nfa.State}
            -> (List nfa.State)
            -> (PrinterState nfa)
            -> (PrinterState nfa)
printNFAFrom [] acc = acc
printNFAFrom (x :: xs) acc = printNFAFrom xs (printState x acc)

export
printNFA : {auto ord : Ordered Char}
        -> (nfa : NA)
        -> {auto ordS : Ordered (nfa .State)}
        -> {auto show: Show nfa.State}
        -> String
printNFA nfa =
"""
digraph finite_state_machine {
rankdir=LR;
size=\"8\"

""" ++ (fastConcat $ reverse $ asList $
          (printNFAFrom all (MkPState [] [<])).acc :< "}")
