import SDP.Value.Nat
import Mathlib.Order.Defs.LinearOrder

/-!
# Max measure for Nat

A `Measure` instance for `List` and `Nat` taking the maximum value.
-/

instance maxMeasure : Measure Nat List where
  measure := List.foldr Nat.max 0
  measure_comp_map_le_measure_comp_map := by
    intros
    intro l
    induction l
    case nil =>
      simp
    case cons h t IH =>
      simp only [Function.comp_apply, List.map_eq_map, List.map_cons, List.foldr_cons]
      simp only [Nat.max_def]
      split
      · split
        · assumption
        · apply le_trans
          · apply IH
          · apply le_of_not_ge
            assumption
      · split
        · case isTrue _ _ _ h1 _ _ =>
          apply le_trans
          · apply h1
          · assumption
        · case isFalse _ _ _ h1 _ _ =>
          apply h1
