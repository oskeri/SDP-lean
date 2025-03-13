import SDP.SDP
import SDP.Value

open StateCtrl

section StateCtrl

variable [sc : StateCtrl]

/-- Policies. A policy provides a `Ctrl` (an action) for each `State`. -/

def Policy (t : Nat) : Type := (s : State t) → Ctrl s

/-- Policy sequences. A policy sequence of length `n` at time `t` is
a list of `n` policies at times `t`, `t+1`, ... `t+n-1` -/

inductive PolicySeq : Nat → Nat → Type
  | nil  : PolicySeq t 0
  | cons : Policy t → PolicySeq (t + 1) n → PolicySeq t (n + 1)

namespace PolicySeq

/-- Empty policy sequences are equal to `nil`. -/

@[simp] lemma eq_nil {ps : PolicySeq t 0} : ps = .nil := match ps with
  | .nil => rfl

/-- Non-empty policy sequences are equal to `cons q qs` for some `q` and `qs`. -/

lemma eq_cons {ps : PolicySeq t (n + 1)} : ∃ q qs, ps = cons q qs := match ps with
  | .cons q qs => by
    repeat (first | constructor | assumption | rfl)

/-- The type of functions that compute policy sequence extensions -/

def ExtFun := {t n : Nat} → PolicySeq (t + 1) n → Policy t


end PolicySeq

end StateCtrl

namespace PolicySeq
open SDP
open Measure

variable {V : Type}
variable {m : Type → Type}
variable [Monad m]
variable [Measure V m]
variable [sdp : SDP V m]


/-- The value of a policy sequence `ps` at a given state `s`. That is, the total
`reward` recieved from applying the policies of `ps`, starting at `s`. -/

def val : PolicySeq t n → State t → V
  | .nil, s => Zero.zero
  | .cons p ps, s =>
    have c := p s
    measure ((reward s c + val ps) <$> next s c)

/-- Compute the value of a policy sequence `ps` given a starting state `s` and a
control `c`. -/

def val' (ps : PolicySeq (t + 1) n) (s : State t) (c : Ctrl s) : V :=
  measure ((reward s c + val ps) <$> next s c)

/-- The value of an empty policy sequence. -/

@[simp] lemma val_nil : val nil s = Zero.zero := by rfl

/-- The value of a non-empty policy sequence. -/

@[simp] lemma val_cons :
  val (cons p ps) s = measure ((reward s (p s) + val ps) <$> next s (p s)) := by rfl

/-- Relating the functions `val` and `val'` -/

lemma val_eq_val' : val (cons p ps) s = val' ps s (p s) := by
  rw [val, val']

/-- A preorder instance for policy sequences. The order is given by the value
of the sequence as given by `val` using the preorder for `Value`. -/

instance : Preorder (PolicySeq t n) where
  le       := fun ps ps'        => val ps ≤ val ps'
  le_refl  := fun _ _           => le_refl _
  le_trans := fun _ _ _ h1 h2 s => le_trans (h1 s) (h2 s)

/-- Optimal policy sequences. A policy sequence is optimal if it is
at least as large as any other (w.r.t its preorder).
-/

def IsOptimalPolicySeq (ps : PolicySeq t n) : Prop :=
  ∀ (ps' : PolicySeq t n), ps' ≤ ps

/-- Optimal extensions of policy sequences. A policy is an optimal
extension if the extended sequence is at least as large as any
other extended sequence (w.r.t its preorder).
-/

def IsOptimalExtension (ps : PolicySeq (t + 1) n) (p : Policy t) : Prop :=
  ∀ (p' : Policy t), cons p' ps ≤ cons p ps

/-- Bellman's optimality principle. An optimal extension of an optimal sequence
is an optimal sequence.
-/

theorem opt_ext_of_opt_policy_seq_is_opt_policy_seq
  {p : Policy t} {ps : PolicySeq (t + 1) n} :
  IsOptimalExtension ps p →
  IsOptimalPolicySeq ps →
  IsOptimalPolicySeq (cons p ps)
  | opt, opt', cons p' ps', s => calc (cons p' ps').val s
    _ = measure ((reward s (p' s) + val ps') <$> next s (p' s)) := by rw [val]
    _ ≤ measure ((reward s (p' s) + val ps)  <$> next s (p' s)) := by
          apply measure_comp_map_le_measure_comp_map
          intro
          apply Value.add_le_add
          · rfl
          · apply opt'
    _ = (cons p' ps).val s                                      := by rw [val]
    _ ≤ (cons p ps).val s                                       := opt _ _


/-- ExtFun:s that compute optimal policy sequence extensions. -/

def IsOptExtFun (f : ExtFun) :=
  ∀ {t n : Nat} (ps : PolicySeq (t + 1) n), IsOptimalExtension ps (f ps)

/-- Compute a policy sequence given an extension function using backwards induction. -/

def policySeq_from_ExtFun (ext : ExtFun) (t n : Nat) : PolicySeq t n :=
  match n with
  | 0     => nil
  | n + 1 =>
    have ps := policySeq_from_ExtFun ext (t + 1) n
    cons (ext ps) ps

/-- The policy sequence given by `policySeq_from_ExtFun` is an optimal policy
sequence if applied to an optimal extension function. -/

theorem OptPolicySeq_from_OptExtFun
  (ext : ExtFun) (isOpt : IsOptExtFun ext) {t n : Nat} :
  IsOptimalPolicySeq (policySeq_from_ExtFun ext t n) := by
  intro ps s
  induction n generalizing t
  case zero =>
    simp
  case succ n IH =>
    apply opt_ext_of_opt_policy_seq_is_opt_policy_seq
    · apply isOpt
    · apply IH

end PolicySeq
