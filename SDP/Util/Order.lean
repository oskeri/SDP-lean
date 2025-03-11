import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Defs.Unbundled

/-- Total and decidable preorders. -/

class TotalDecPreorder (A : Type) extends Preorder A, IsTrichotomous A (· < ·) where
  dec : @DecidableRel A A (· < ·)

/-- Instance declaration for decidability. -/

instance [TotalDecPreorder A] : @DecidableRel A A (· < ·) :=
  TotalDecPreorder.dec

instance [TotalDecPreorder V] : Preorder V := inferInstance
