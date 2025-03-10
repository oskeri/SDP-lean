import SDP.SDP
import SDP.Value

open StateCtrl

section StateCtrl

variable [sc : StateCtrl]

def Policy (t : Nat) : Type := (s : State t) → Ctrl s

inductive PolicySeq : Nat → Nat → Type
  | nil  : PolicySeq t 0
  | cons : Policy t → PolicySeq (t + 1) n → PolicySeq t (n + 1)

end StateCtrl

namespace PolicySeq
open SDP
open Value

variable {V : Type}
variable [Value V]
variable {m : Type → Type}
variable [Monad m]
variable [SDP V m]


def val : PolicySeq t n → State t → V
  | .nil, s => Zero.zero
  | .cons p ps, s =>
    have c := p s
    measure ((reward s c + val ps) <$> next s c)

-- A preorder for policy sequences

instance : Preorder (PolicySeq t n) where
  le       := fun ps ps'        => val ps ≤ val ps'
  le_refl  := fun _ _           => le_refl _
  le_trans := fun _ _ _ h1 h2 s => le_trans (h1 s) (h2 s)

def OptimalPolicySeq (ps : PolicySeq t n) : Prop :=
  ∀ (ps' : PolicySeq t n), ps' ≤ ps

def OptimalPolicyExtension (ps : PolicySeq (t + 1) n) (p : Policy t) : Prop :=
  ∀ (p' : Policy t), cons p' ps ≤ cons p ps

theorem opt_ext_of_opt_policy_seq_is_opt_policy_seq
  {p : Policy t} {ps : PolicySeq (t + 1) n} :
  OptimalPolicyExtension ps p →
  OptimalPolicySeq ps →
  OptimalPolicySeq (cons p ps)
  | opt, opt', cons p' ps', s => calc (cons p' ps').val s
    _ = measure ((reward s (p' s) + val ps') <$> next s (p' s)) := by rw [val]
    _ ≤ measure ((reward s (p' s) + val ps) <$> next s (p' s))  := by
          apply measure_comp_map_le_measure_comp_map
          intro
          apply Value.add_le_add
          · rfl
          · apply opt'
    _ = (cons p' ps).val s                                      := by rw [val]
    _ ≤ (cons p ps).val s                                       := opt _ _

end PolicySeq
