import Init.Data.Vector.Basic
import Batteries.Data.List.Basic
import Mathlib.Data.FinEnum
import Mathlib.Data.FinEnum.Option
import SDP.SDP
import SDP.Value.Nat
import SDP.Value.Nat.Max
import SDP.Policy.FinEnum
import SDP.Trajectory

/-!
# Tic-tac-toe

A silly example modelling a variant of tic-tac-toe as an SDP.

There are two players, `X` and `O` with `X` being the opponent.

At each time step, the decision (`Ctrl`) is where to put an `O` or to pass.
The transition function returns a list of possible boards for all possible moves
that the opponent can make (the opponent is assumed to never pass). The score is
given by the number of lines a player has. The player tries to maximize the score
(i.e. the measure function is `max`).

## Implementation notes

This code can be improved in several ways.

-/

namespace TicTacToe
open StateCtrl

/-- A cell is either blank or occupied by one of the players. -/

inductive Cell : Type
  | Blank : Cell
  | X : Cell
  | O : Cell
  deriving DecidableEq

/-- a `ToString` instance for `Cell`. -/

instance : ToString Cell where
  toString
  | .Blank => " "
  | .X => "X"
  | .O => "O"

/-- A board is a 3x3 matrix of cells.-/

abbrev Board := Vector (Vector Cell 3) 3

/-- Convert a `Board` to a `List (List Cell)` -/

def toListList (b : Board) : List (List Cell) :=
  List.map (fun x => x.toList) b.toList

/-- `ToString` instance for `State` -/

instance instToStringState : ToString Board where
  toString b := toString (toListList b)

/-- The board contatining only blanks. -/

def blank_board : Board where
  toList := [blankRow,blankRow,blankRow]
  size_toArray := by trivial
  where
  blankRow : Vector Cell 3 := {
    toList := [.Blank,.Blank,.Blank]
    size_toArray := by trivial
  }
def all_positions : List (Nat × Nat) :=
  [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]


/-- Does a row score a point for a given player. -/

def winRow (c : Cell) (r : List Cell) : Bool :=
  List.all r (· == c)

/-- Get a list of all "rows" that can score. -/

def allRows (b : Board) : List (List Cell) :=
  have b' := toListList b
  have d1 :=
    [Vector.get (Vector.get b 0) 0,
     Vector.get (Vector.get b 1) 1,
     Vector.get (Vector.get b 2) 2,
    ]
  have d2 :=
    [Vector.get (Vector.get b 0) 2,
     Vector.get (Vector.get b 1) 1,
     Vector.get (Vector.get b 2) 0,
    ]
  b' ++ b'.transpose ++ [d1, d2]

/-- Compute the score of a player. -/

def score (c : Cell) (b : Board) : Nat :=
  (List.filter id (List.map (winRow c) (allRows b))).length

/-- Attempt to fill in a cell of the board for a given player if not
already occupied. -/

def fill (c : Cell) (b : Board) (x y : Fin 3) : Option Board :=
  if Vector.get (Vector.get b x) y == .Blank
    then some (Vector.set b x (Vector.set (Vector.get b x) y c))
    else none

/-- Play a round for the opponent. Returing a list of all possible plays. -/

def play (c : Cell) (b : Board) : List Board :=
  let idx := all_positions
  List.reduceOption (List.map (fun (x,y) => fill c b x y) idx)

/-- The type of controls are positions which are not yet filled. -/

structure Ctrl (b : Board) : Type where
  x : Fin 3
  y : Fin 3
  isBlank : Vector.get (Vector.get b x) y = .Blank
  deriving DecidableEq

/-- A `ToString` instance for `Ctrl`. -/

instance instToStringControl (s : Board) : ToString (Ctrl s) where
  toString c := "(" ++ toString (c.x) ++ "," ++ toString (c.y) ++ ")"

/-- The type `Option Ctrl` is nonempty. -/

instance Nonempty_Control (s : Board) : Nonempty (Option (Ctrl s)) :=
  .intro none

/-- A function used to prove that `Option (Ctrl s)` is finitely enumerable. -/

def toCtrl : Option (Fin 3 × Fin 3) → Option (Ctrl s)
  | .none => none
  | .some (x, y) =>
      match decEq (Vector.get (Vector.get s x) y) .Blank with
      | .isFalse _ => none
      | .isTrue h => some {
        x := x
        y := y
        isBlank := h
      }

/-- The type `Control` is finitely enumerable. -/

instance FinEnum_Ctrl (s : Board) : FinEnum (Option (Ctrl s)) :=
  FinEnum.ofSurjective (β := Option (Fin 3 × Fin 3)) toCtrl (by
    intro
    | none =>
      apply Exists.intro none
      rfl
    | some { x := x, y := y, isBlank := h} =>
      apply Exists.intro (some (x,y))
      unfold toCtrl
      split
      case h_1 => contradiction
      case h_2 eq =>
      match eq with
      | rfl =>
      split
      · contradiction
      · rfl
  )

/-- The type `Control` is Nonempty. -/

instance Nonempty_Ctrl (s : Board) : Nonempty (Option (Ctrl s)) :=
  .intro none

instance GHG_TicTacToe : SDP Nat List where
  State _ := Board
  Ctrl s := Option (Ctrl s)
  next {t} s c :=
    c.elim [s] (fun c =>
      play .X (Vector.set s c.x (Vector.set (Vector.get s c.x) c.y .O)))
  reward _ _ s := score .O s

/-- `ToStringStateCtrl` instance for the SDP -/

instance instToStringStateCtrl : ToStringStateCtrl GHG_TicTacToe.toStateCtrl where
  toStringState := toString (self := instToStringState)
  toStringCtrl := toString (self := instToStringOption)

/-- The optimal policy sequence for the SDP -/

def GHG_policySeq (t n : Nat) : PolicySeq t n :=
  FinEnum.bestPolicySeq FinEnum_Ctrl Nonempty_Ctrl t n

/-- The trajectory of the optimal sequence. -/

def GHG_trj (t n : Nat) (s : Board) : List (Trj t (n + 1)) :=
  Trj.trj (GHG_policySeq t n) s

/-- The value of the optimal sequence. -/

def GHG_val (t n : Nat) (s : Board) : Nat :=
  PolicySeq.val (GHG_policySeq t n) s

-- Display the optimal trajectory
-- Note that running this until the board is full (t = 5) takes very long.
#eval GHG_trj 0 1 blank_board

-- Display the optimal value
-- Note that running this until the board is full (t = 5) takes very long.
#eval GHG_val 0 1 blank_board
