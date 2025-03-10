
import Mathlib.Data.FinEnum
import Mathlib.Data.List.MinMax
import Mathlib.Order.Defs.PartialOrder
import SDP.Util.FinEnum
import SDP.Util.TotalPreorder

class Argmax (A B : Type) extends Preorder B where
  argmax : (A → B) → A
  le_argmax (f : A → B) (a : A) : f a ≤ f (argmax f)

namespace Argmax

def argmax' [FinEnum A] [Nonempty A] [Preorder B] [@DecidableRel B B (· < ·)] (f : A → B) : A :=
  match h : List.argmax f (FinEnum.toList A) with
    | some a => a
    | none => by
      exfalso
      apply @FinEnum.toList_neq_nil A
      rw [List.argmax_eq_none] at h
      assumption

lemma argmax'_mem_argmax [FinEnum A] [Nonempty A] [Preorder B] [@DecidableRel B B (· < ·)]
  (f : A → B) : argmax' f ∈ List.argmax f (FinEnum.toList A) := sorry

  -- unfold argmax'
  -- match h : List.argmax f (FinEnum.toList A) with
  -- | some a =>
  --   unfold argmax'
  --   simp [h]

  -- | none => sorry

instance argmax_of_finEnum [FinEnum A] [Nonempty A] [TotalPreorder B] : Argmax A B where
  argmax := argmax'
  le_argmax f a := by
    match @trichotomous B (· < ·) _ (f a) (f (argmax' f)) with
      | .inl h =>
        apply le_of_lt
        assumption
      | .inr (.inl h) => rw [h]
      | .inr (.inr h) =>
        exfalso
        apply List.not_lt_of_mem_argmax _ _ h
        · exact FinEnum.toList A
        · apply FinEnum.mem_toList
        · apply argmax'_mem_argmax
