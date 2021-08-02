module NFA.PrettyPrint
import NFA
import Data.List
import Data.SnocList
import public NFA.PrettyPrint.Interfaces


transitionString : {auto nfa : NA} -> {auto s: Show nfa.State}
                -> nfa.State -> Char -> nfa.State -> String
transitionString s c t =
  (show s) ++ " -> " ++ (show t) ++ "[label = \"" ++ cast c ++ "\"];\n"

printNodeStyleString : {auto nfa : NA} -> {auto s: Show nfa.State}
                  -> nfa.State -> String
printNodeStyleString s =
  let _ := nfa.isEq
      color : String
      color = case (find (==s) nfa.start) of
                Nothing => "black"
                (Just _) => "red"
      circle : String
      circle = if (nfa.accepting s)
               then "doublecircle"
               else "circle"
  in "node [shape = " ++ circle ++
        ", color = " ++ color ++"]; "
        ++ (show s) ++ ";\n"

record PrinterState (nfa : NA) where
  constructor MkPState
  seenStates : List (nfa .State)
  acc : SnocList String

printNodeStyle : {auto nfa : NA}
            -> {auto show: Show nfa.State}
            -> nfa.State
            -> (PrinterState nfa)
            -> (PrinterState nfa)
printNodeStyle s (MkPState seenStates acc) =
  MkPState (s::seenStates) (acc :< (printNodeStyleString s))

printTransition : {auto nfa : NA}
                -> {auto show: Show nfa.State}
                -> nfa.State
                -> Char -> nfa.State
                -> (PrinterState nfa) -> (PrinterState nfa)
printTransition s c t (MkPState seenStates acc) =
  MkPState seenStates (acc :< transitionString s c t)

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
