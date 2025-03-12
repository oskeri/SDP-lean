
import Mathlib.Data.FinEnum
import Mathlib.Data.List.MinMax
import Mathlib.Order.Defs.PartialOrder
import SDP.Util.Order

/-- `Argmax A B` for a preorder B denotes that one can always find `a : A`
such that `f a` is an upper bound of values in the image of any `f : A → B`
-/

class Argmax (A B : Type) [Preorder B] where
  argmax : (A → B) → A
  le_argmax (f : A → B) (a : A) : f a ≤ f (argmax f)

namespace List

/-- A version of `argmax` for non-empty lists. -/

def argmax_nonempty [Preorder B] [@DecidableRel B B (· < ·)]
  (f : A → B) (l : List A) (nonempty : l ≠ []) : A :=
  match h : argmax f l with
  | some a => a
  | none => by
    exfalso
    apply nonempty
    rw [argmax_eq_none] at h
    assumption

/-- `argmax_nonempty` gives the argument that maximizes `f` of all
elements in the list. -/

theorem le_argmax_nonempty [TotalDecPreorder B]
  (f : A → B) (l : List A) (nonempty : l ≠ []) :
  a ∈ l → f a ≤ f (argmax_nonempty f l nonempty) := by
  intro mem
  match @trichotomous B (· < ·) _ (f a) (f (argmax_nonempty f l nonempty)) with
  | .inl h =>
    apply le_of_lt
    assumption
  | .inr (.inl h) =>
    rw [h]
  | .inr (.inr h) =>
    exfalso
    apply not_lt_of_mem_argmax _ _ h
    · exact l
    · exact mem
    · unfold argmax_nonempty
      split
      · case h_1 a h' =>
        rw [h']
        trivial
      · case h_2 h' =>
        exfalso
        apply nonempty
        rw [argmax_eq_none] at h'
        assumption

end List
