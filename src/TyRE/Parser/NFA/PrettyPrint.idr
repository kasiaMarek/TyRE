module TyRE.Parser.NFA.PrettyPrint

import Data.List
import Data.SnocList

import TyRE.Parser.NFA
import public TyRE.Parser.NFA.PrettyPrint.Interfaces

transitionString : String -> String -> String -> String
transitionString from label to =
  from ++ " -> " ++ to ++ "[label = \"" ++ label ++ "\"];\n"

makeTransitionString : {auto nfa : NA} -> {auto s : Show nfa.State}
                -> (Maybe nfa.State) -> Char -> (Maybe nfa.State) -> String
makeTransitionString s c t = transitionString (show s) (cast c) (show t)
  --(show s) ++ " -> " ++ (show t) ++ "[label = \"" ++ cast c ++ "\"];\n"

nodeStyleString : String -> String -> String
nodeStyleString shape name =
  "node [shape = " ++ shape ++ "]; "
      ++ name ++ ";\n"

printNodeStyleString : {auto nfa : NA} -> {auto s : Show nfa.State}
                  -> Maybe nfa.State -> String
printNodeStyleString Nothing = nodeStyleString "doublecircle" "."
printNodeStyleString (Just s) = nodeStyleString "doublecircle" (show s)

record PrinterState (nfa : NA) where
  constructor MkPState
  seenStates : List (Maybe nfa .State)
  acc : SnocList String

printNodeStyle : {auto nfa : NA}
            -> {auto sh: Show nfa.State}
            -> (Maybe nfa.State)
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
                -> {auto sh : Show nfa.State}
                -> (Maybe nfa.State)
                -> Char -> (Maybe nfa.State)
                -> (PrinterState nfa) -> (PrinterState nfa)
printTransition s c t (MkPState seenStates acc) =
  MkPState seenStates (acc :< makeTransitionString s c t)

printTransitionsFrom : {auto nfa : NA}
                    -> {auto show : Show nfa.State}
                    -> (Maybe nfa.State)
                    -> Char -> List (Maybe nfa.State)
                    -> (PrinterState nfa) -> (PrinterState nfa)
printTransitionsFrom s c [] ps = ps
printTransitionsFrom s c (t :: ss) ps =
  let _ := nfa.isEq
      currPs := case find (==t) ps.seenStates of
                    Nothing => printNodeStyle t ps
                    (Just _) => ps
  in printTransitionsFrom s c ss (printTransition s c t currPs)

printTransitions : {auto nfa : NA} -> {auto show : Show nfa.State}  -> (Maybe nfa.State)
                -> List Char
                -> (PrinterState nfa) -> (PrinterState nfa)
printTransitions s [] ps = ps
printTransitions s (c :: cs) ps = printTransitionsFrom s c (liftNext nfa.next s c) ps

printState : {auto ord : Ordered Char}
          -> {auto nfa : NA}
          -> {auto show : Show nfa.State}
          -> (Maybe nfa.State)
          -> (PrinterState nfa)
          -> (PrinterState nfa)
printState x ps =
  let _ := nfa.isEq
  in case find (==x) ps.seenStates of
      Nothing => printTransitions x all (printNodeStyle x ps)
      (Just y) => printTransitions x all ps

printNFAFrom : {auto ord : Ordered Char}
            -> {auto nfa : NA}
            -> {auto show : Show nfa.State}
            -> (List (Maybe nfa.State))
            -> (PrinterState nfa)
            -> (PrinterState nfa)
printNFAFrom [] acc = acc
printNFAFrom (x :: xs) acc = printNFAFrom xs (printState x acc)

export
printNFA : {auto ord : Ordered Char}
        -> (nfa : NA)
        -> {auto ordS : Ordered (Maybe nfa .State)}
        -> {auto show : Show nfa.State}
        -> String
printNFA nfa =
"""
digraph finite_state_machine {
rankdir=LR;
size=\"8\"

""" ++ (fastConcat $ reverse $ asList $
          (printNFAFrom all (MkPState [] [<])).acc :< "}")
