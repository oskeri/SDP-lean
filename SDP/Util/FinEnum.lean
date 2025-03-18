import Mathlib.Data.FinEnum
import SDP.Util.Argmax
import SDP.Util.Order

/-!
# FinEnum

This file provides an `Argmax` instance for Finitly enumerable, nonempty types given
a total and decidable preorder.

-/

namespace FinEnum

/-- The length of `FinEnum.toList A` is equal to `FinEnum.card`. -/

theorem length_toList_eq_card [FinEnum A] : List.length (toList A) = card A := by
  simp [FinEnum.toList.eq_1, List.length_finRange]

/-- `FinEnum.toList A` is not equal to `[]`. -/

theorem toList_neq_nil [FinEnum A] [Nonempty A] : toList A ≠ [] := by
  intro h
  apply @FinEnum.card_ne_zero A
  rw [← length_toList_eq_card, h, List.length_nil]

/-- An instance of `Argmax A B` for non-empty, finite enumerable type `A` and totally
preordered type `B`. -/

instance argmax [FinEnum A] [Nonempty A] [TotalDecPreorder B] : Argmax A B where
  argmax f :=
    List.argmax_nonempty f (FinEnum.toList A) FinEnum.toList_neq_nil
  le_argmax f a :=
    List.le_argmax_nonempty f (FinEnum.toList A)
      FinEnum.toList_neq_nil (FinEnum.mem_toList a)
