import SDP.Util.Order
import SDP.Util.Argmax
import SDP.Util.FinEnum

/-!
# Value types

This file defines values and measurable values.

-/

/-- A value type has a "zero" element and a preorder.
Addition is monotone. Note that the zero element is not assumed
to be the unit of addition.-/

class Value (V : Type) extends Add V, Zero V, TotalDecPreorder V where
  add_le_add : {a b c d : V} → a ≤ b → c ≤ d → a + c ≤ b + d

/-- Values with a `measure` function. -/

class Measure (V : Type) (m : Type → Type) [Monad m] extends Value V where
  /-- A monotone aggregation function for values in the monad. -/
  measure : m V → V
  measure_comp_map_le_measure_comp_map :
    f ≤ g → measure ∘ (Functor.map f) ≤ measure ∘ (Functor.map g)

namespace Value

/-- Lifting the addition to functions with values as codomain. -/

instance {A V : Type} [Value V] : Add (A → V) where
  add := fun f g a => f a + g a

/-- Lifting the preorder to functions -/

instance {A V : Type} [Value V] : Preorder (A → V) where
  le := fun f g => ∀ a, f a ≤ g a
  le_refl := fun f a => le_refl _
  le_trans := fun f g h h1 h2 a => le_trans (h1 a) (h2 a)

/-- Functions into values support an argmax function for certain domains. -/

instance argmax [FinEnum A] [Nonempty A] [Value V] : Argmax A V := FinEnum.argmax

end Value
