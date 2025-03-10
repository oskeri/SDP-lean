import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Defs.Unbundled


/-- Total preorders. -/

class TotalPreorder (A : Type) extends Preorder A, IsTrichotomous A (· < ·)

namespace TotalPreorder

/-- The order of total preorders is decidable. -/

instance [self : TotalPreorder A] : @DecidableRel A A (· < ·) :=
  fun a b => by
    simp
    admit
--     cases @trichotomous A (· < ·) _ a b with
--     | inl h =>
--       sorry
--       -- exact isTrue h
--     | inr h => sorry

-- #check TotalPreorder
