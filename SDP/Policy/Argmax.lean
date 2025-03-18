
import SDP.SDP
import SDP.Policy
import SDP.Util.Argmax

/-!
# Policy.Argmax

This file finds optimal policy sequences for SDP:s with an `Argmax` instance
for controls and values.

-/

namespace Argmax

open StateCtrl
open PolicySeq

variable {V : Type}
variable {m : Type → Type}
variable [Monad m]
variable [Measure V m]
variable [sdp : SDP V m]

variable (argmax : {t : Nat} → (s : State t) → Argmax (Ctrl s) V)

/-- If `Argmax (Ctrl s) V` for every `s : State t` then one can define
a policy extension function. -/

def extFun : ExtFun :=
  fun ps s =>
    Argmax.argmax (self := (argmax s)) (val' ps s)

/-- The policy extension function given by `extFun` is optimal. -/

lemma IsOptExtFun_extFun : IsOptExtFun (extFun argmax) := by
  repeat intro
  rw [val_eq_val', val_eq_val' (p := extFun argmax _)]
  apply Argmax.le_argmax

/-- If `Argmax (Ctrl s) V` for every `s : State t` then one can construct a
policy sequence of any length. -/

def bestPolicySeq (t n : Nat) : PolicySeq t n :=
  policySeq_from_ExtFun (extFun argmax) t n

/-- The policy sequence `bestPolicySeq` is optimal. -/

theorem optimal_bestPolicySeq : IsOptimalPolicySeq (bestPolicySeq argmax t n) := by
  simp [bestPolicySeq]
  apply OptPolicySeq_from_OptExtFun
  apply IsOptExtFun_extFun
