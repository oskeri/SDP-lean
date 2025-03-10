import Mathlib.Data.FinEnum

namespace FinEnum

/-- The length of `FinEnum.toList A` is equal to `FinEnum.card`. -/

theorem length_toList_eq_card [FinEnum A] : List.length (toList A) = card A := by
  simp [FinEnum.toList.eq_1, List.length_finRange]

/-- `FinEnum.toList A` is not equal to `[]`. -/

theorem toList_neq_nil [FinEnum A] [Nonempty A] : toList A ≠ [] := by
  intro h
  apply @FinEnum.card_ne_zero A
  rw [← length_toList_eq_card, h, List.length_nil]
