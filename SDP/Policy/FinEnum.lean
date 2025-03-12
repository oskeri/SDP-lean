
import SDP.SDP
import SDP.Policy
import SDP.Policy.Argmax
import SDP.Util.FinEnum

namespace FinEnum

open StateCtrl
open PolicySeq

variable {V : Type}
variable [Value V]
variable {m : Type → Type}
variable [Monad m]
variable [sdp : SDP V m]

variable (finEnum : {t : Nat} → (s : State t) → FinEnum (Ctrl s))
variable (nonempty : {t : Nat} → (s : State t) → Nonempty (Ctrl s))

/-- If `FinEnum (Ctrl s)` and `Nonempty (Ctrl s)` for every `s : State t` then one can define
a policy extension function. -/

def extFun : ExtFun :=
    Argmax.extFun (fun _ => FinEnum.argmax)

/-- The policy extension function given by `extFun` is optimal. -/

lemma IsOptExtFun_extFun : IsOptExtFun (extFun finEnum nonempty) :=
    Argmax.IsOptExtFun_extFun (fun _ => FinEnum.argmax)

/-- If `FinEnum (Ctrl s)` and `Nonempty (Ctrl s)` for every `s : State t`
then one can construct a policy sequence of any length. -/

def bestPolicySeq (t n : Nat) : PolicySeq t n :=
  Argmax.bestPolicySeq (fun _ => FinEnum.argmax) t n

/-- The policy sequence `bestPolicySeq` is optimal. -/

theorem optimal_bestPolicySeq : IsOptimalPolicySeq (bestPolicySeq finEnum nonempty t n) :=
    Argmax.optimal_bestPolicySeq (fun _ => FinEnum.argmax)
