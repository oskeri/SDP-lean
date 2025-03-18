import SDP.Value
import SDP.Monad.SP
import Mathlib.Tactic

/-!
# Rational number values

This file defines a `Value` instance for `Rat` as well as a `Measure`
instance using the `SP` monad with the exectation value as `measure`.

-/

namespace Rat

/-- `Value` instance for `Rat`. -/

instance value : Value Rat where
  add_le_add := add_le_add
  dec := instDecidableLt

/-- Weighted sum for the `SP` monad. -/

def wSum : SP Rat → Rat
  | .mkSP l => List.foldr (fun (w, v) acc => w * v + acc) 0 l

/-- `wSum` preserves monotonicity of functions. -/

lemma wSum_map_le_wSum_map (f g : A → Rat) (l : SP A) :
  f ≤ g → wSum (SP.map f l) ≤ wSum (SP.map g l) := by
  intro h
  repeat rw [← SP.map_eq_map,SP.map_eq_ap_map]
  match l with
  | .mkSP l =>
  simp [wSum]
  induction l
  case nil =>
    trivial
  case cons _ _ IH =>
    simp
    apply add_le_add
    · apply OrderedSemiring.mul_le_mul_of_nonneg_left
      · apply h
      · simp
    · assumption

/-- `Measure` instance for `Rat` with the `SP` monad using the expectation
value as `measure`. -/

instance measure_ev : Measure Rat SP where
  measure l := wSum l / SP.totalWeight l
  measure_comp_map_le_measure_comp_map := by
    intro _ f g le l
    simp [Rat.div_def]
    apply OrderedSemiring.mul_le_mul_of_nonneg_right
    · exact wSum_map_le_wSum_map _ _ _ le
    · simp [inv_def]
