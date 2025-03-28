import SDP.SDP
import SDP.Policy

/-!
# Trajectories

This file defines trajectories representing the transition of states.
The primary purposes of trajectories is to visualize the solution of an SDP.
-/

open StateCtrl
open ToStringStateCtrl

section StateCtrl

variable [sc : StateCtrl]

/-- Trajectories -/

inductive Trj : Nat → Nat → Type
  | sg : State t → Trj t 1
  | cons : (s : State t) → Ctrl s → Trj (t + 1) (n + 1) → Trj t (n + 2)
namespace Trj

/-- The first state of a trajectory. -/

def first : Trj t n → State t
  | sg s => s
  | cons s _ _ => s

/-- There are no trajectories of length 0. -/

instance instIsEmpty : IsEmpty (Trj t 0) := by
  constructor
  intro tr
  nomatch tr

/-- A `ToString` instance for `Trj`. -/

instance instToString [ToStringStateCtrl sc] : ToString (Trj t n) where
  toString := toString'
  where
  toString' {t n : Nat} : Trj t n → String
    | sg s => toStringState s
    | cons s c tr =>
      toStringState s ++ " →⟨ " ++ toStringCtrl c ++ " ⟩ " ++ toString' tr

end Trj
end StateCtrl

namespace Trj

open SDP
open Measure

variable {V : Type}
variable {m : Type → Type}
variable [Monad m]
variable [Measure V m]
variable [SDP V m]

/-- Compute the trajctories of a policy sequence starting at a state. -/

def trj : PolicySeq t n → State t → m (Trj t (n + 1))
  | .nil, s => pure (sg s)
  | .cons p ps, s =>
    have c := p s
    (cons s c) <$> (next s c >>= trj ps)

/-- Compute the total value of a trajectory. -/

def sumTrj : Trj t n → V
  | sg s => Zero.zero
  | cons s c tr => reward s c (first tr) + sumTrj tr

/-- Compute the value of a policy sequence. -/

def val (ps : PolicySeq t n) : (s : State t) → V :=
  measure ∘ Functor.map sumTrj ∘ trj ps
