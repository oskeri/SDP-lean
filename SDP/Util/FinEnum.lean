import Mathlib.Data.FinEnum

namespace FinEnum

-- This does not belong here but I refuse to believe that this is not proven elsewhere already

lemma length_map_eq_length {l : List A} {f : A → B} : (List.map f l).length = l.length := by
  induction l
  · case nil =>
    unfold List.map
    rfl
  · case cons h t IH =>
    unfold List.map
    unfold List.length
    rw [IH]

theorem length_toList_eq_card [FinEnum A] : List.length (toList A) = card A := by
  rw [FinEnum.toList.eq_1, length_map_eq_length, List.length_finRange]

theorem toList_neq_nil [FinEnum A] [Nonempty A] : toList A ≠ [] := by
  intro h
  apply @FinEnum.card_ne_zero A
  rw [← length_toList_eq_card, h, List.length_nil]
