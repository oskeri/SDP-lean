import SDP.SDP
import SDP.Policy

open StateCtrl

section StateCtrl

variable [sc : StateCtrl]

inductive Trj : Nat → Nat → Type
  | sg : State t → Trj t 1
  | cons : (s : State t) → Ctrl s → Trj (t + 1) (n + 1) → Trj t (n + 2)

namespace Trj

def head : Trj t n → State t
  | sg s => s
  | cons s _ _ => s

end Trj
end StateCtrl

namespace Trj

open SDP
open Value

variable {V : Type}
variable [Value V]
variable {m : Type → Type}
variable [Monad m]
variable [SDP V m]

def trj : PolicySeq t n → State t → m (Trj t (n + 1))
  | .nil, s => pure (sg s)
  | .cons p ps, s =>
    have c := p s
    (cons s c) <$> (next s c >>= trj ps)

def sumTrj : Trj t n → V
  | sg s => Zero.zero
  | cons s c tr => reward s c (head tr) + sumTrj tr

def val (ps : PolicySeq t n) : (s : State t) → V :=
  measure ∘ Functor.map sumTrj ∘ trj ps
