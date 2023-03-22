module TyRE.Parser.PrettyPrinter

import TyRE.Parser.SM
import Data.List
import Data.SnocList
import Data.Fin

public export
interface Ordered ty where
  constructor MkOrdered
  all : List ty

transitionString : String -> String -> String -> String
transitionString from label to =
  from ++ " -> " ++ to ++ "[label = \"" ++ label ++ "\"];\n"

makeTransitionString : {auto mm : SM x} -> {shw : Show (Maybe mm.s)}
                -> (Maybe mm.s) -> Char -> (Maybe mm.s) -> String
makeTransitionString s c t = transitionString (show s) (cast c) (show t)

nodeStyleString : String -> String -> String
nodeStyleString shape name =
  "node [shape = " ++ shape ++ "]; "
      ++ name ++ ";\n"

printNodeStyleString : {auto mm : SM x} -> {shw : Show (Maybe mm.s)}
                  -> Maybe mm.s -> String
printNodeStyleString s = nodeStyleString "doublecircle" (show s)

record PrinterState (mm : SM x) where
  constructor MkPState
  seenStates : List (Maybe mm.s)
  acc : SnocList String

printNodeStyle : {auto mm : SM x}
            -> {shw: Show (Maybe mm.s)}
            -> (Maybe mm.s)
            -> (PrinterState mm)
            -> (PrinterState mm)
printNodeStyle s (MkPState seenStates acc) =
  let _ := mm.isEq
      currentAcc :=
        case find (== s) (map fst mm.init) of
          Nothing => acc :< (printNodeStyleString {shw} s)
          Just _ =>
            acc :< (printNodeStyleString {shw} s)
                :< (transitionString "start" "start" (show s))
  in MkPState (s::seenStates) currentAcc

printTransition : {auto mm : SM x}
                -> {shw : Show (Maybe mm.s)}
                -> (Maybe mm.s)
                -> Char -> (Maybe mm.s)
                -> (PrinterState mm) -> (PrinterState mm)
printTransition s c t (MkPState seenStates acc) =
  MkPState seenStates (acc :< makeTransitionString {shw} s c t)

printTransitionsFrom : {auto mm : SM x}
                    -> {shw : Show (Maybe mm.s)}
                    -> (Maybe mm.s)
                    -> Char -> List (Maybe mm.s)
                    -> (PrinterState mm) -> (PrinterState mm)
printTransitionsFrom s c [] ps = ps
printTransitionsFrom s c (t :: ss) ps =
  let _ := mm.isEq
      currPs := case find (==t) ps.seenStates of
                    Nothing => printNodeStyle {shw} t ps
                    (Just _) => ps
  in printTransitionsFrom {shw} s c ss (printTransition {shw} s c t currPs)

printTransitions : {auto mm : SM x} -> {shw : Show (Maybe mm.s)} -> (Maybe mm.s)
                -> List Char -> (PrinterState mm) -> (PrinterState mm)
printTransitions s [] ps = ps
printTransitions Nothing (c :: cs) ps = ps
printTransitions (Just s) (c :: cs) ps =
  printTransitionsFrom {shw} (Just s) c (map fst (mm.next s c)) ps

printState : {auto ord : Ordered Char}
          -> {auto mm : SM x}
          -> {shw : Show (Maybe mm.s)}
          -> (Maybe mm.s)
          -> (PrinterState mm)
          -> (PrinterState mm)
printState x ps =
  let _ := mm.isEq
  in case find (==x) ps.seenStates of
      Nothing => printTransitions {shw} x all (printNodeStyle {shw} x ps)
      (Just y) => printTransitions {shw} x all ps

printNFAFrom : {auto ord : Ordered Char}
            -> {auto mm : SM x}
            -> {shw : Show (Maybe mm.s)}
            -> (List (Maybe mm.s))
            -> (PrinterState mm)
            -> (PrinterState mm)
printNFAFrom [] acc = acc
printNFAFrom (x :: xs) acc = printNFAFrom {shw} xs (printState {shw} x acc)


makeListOfStatesRec : {auto ord : Ordered Char} -> (mm : SM x) -> (toNext : List (Maybe mm.s)) -> (acc : List (Maybe mm.s)) -> List (Maybe mm.s)
makeListOfStatesRec mm [] acc = acc
makeListOfStatesRec mm (Nothing :: xs) acc =
  let _ := mm.isEq
  in case find (== Nothing) acc of
      Nothing => makeListOfStatesRec mm xs (Nothing :: acc)
      (Just y) => makeListOfStatesRec mm xs acc
makeListOfStatesRec mm ((Just x) :: xs) acc =
  let _ := mm.isEq
  in case find (== (Just x)) acc of
      (Just _) => makeListOfStatesRec mm xs acc
      Nothing => makeListOfStatesRec mm (xs ++ (all >>= (\c => map fst (mm.next x c)))) (Just x :: acc)

makeListOfStates : {auto ord : Ordered Char} -> (mm : SM x) -> List (Maybe mm.s)
makeListOfStates mm = makeListOfStatesRec mm (map fst mm.init) []

showS : {0 a : Type} -> {auto eq : Eq a} -> List a -> a -> String
showS xs x {eq} =
  case findIndex ( == x ) xs of
    Nothing => "OUT"
    (Just y) => show (finToNat y)

export
printNFA : {auto ord : Ordered Char}
        -> (mm : SM x)
        -> String
printNFA mm =
  let _ := mm.isEq
      ordS : Ordered (Maybe mm.s)
      ordS = MkOrdered (makeListOfStates mm)
      _ := ordS
      show : Show (Maybe mm.s)
      show = MkShow (showS all) (\_ => showS all)
  in """
    digraph finite_state_machine {
    rankdir=LR;
    size=\"8\"
    """ ++ (fastConcat $ reverse $ asList $
              (printNFAFrom {mm} all {shw = show} (MkPState [] [<])).acc :< "}")