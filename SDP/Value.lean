-- Values for SDP:s

import SDP.Util.Order
import SDP.Util.Argmax

-- A Value type has addition,

/-- A value type has a "zero" element and a preorder.
Addition is monotone. Note that the zero element is not assumed
to be the unit of addition.-/

class Value (V : Type) extends Add V, Zero V, TotalPreorder V where
  add_le_add : ∀ a b c d : V, a ≤ b → c ≤ d → a + c ≤ b + d

namespace Value

-- TODO: Is is possible to get rid of this?
instance [Value V] : Preorder V := TotalPreorder.toPreorder
instance [Value V] : LE V := Preorder.toLE

/-- Lifting the addition to functions with values as codomain. -/

instance {A V : Type} [Value V] : Add (A → V) where
  add := fun f g a => f a + g a

namespace Preorder

/-- Lifting the preorder to functions -/

instance {A V : Type} [Value V] : Preorder (A → V) where
  le := fun f g => ∀ a, f a ≤ g a
  le_refl := fun f a => le_refl _
  le_trans := fun f g h h1 h2 a => le_trans (h1 a) (h2 a)

end Preorder

/-- Functions into values support an argmax function for certain domains. -/

instance argmax_value [FinEnum A] [Nonempty A] [Value V] : Argmax A V := Argmax.argmax_of_finEnum

end Value
