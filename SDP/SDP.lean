
import SDP.Value

class StateCtrl where
  State : Nat → Type
  Ctrl  : State t → Type

class SDP (V : Type) (m : Type → Type) [Value V] [Monad m] extends StateCtrl where
  next  : (s : State t) → Ctrl s → m (State (t + 1))
  reward : (s : State t) → Ctrl s → State (t + 1) → V
  -- A monotone aggregation function for values in the monad
  measure : m V → V
  measure_comp_map_le_measure_comp_map :
    f ≤ g → measure ∘ (Functor.map f) ≤ measure ∘ (Functor.map g)
