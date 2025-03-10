
import SDP.Value

/-- States and Controls. States are a representation of the system at
a given time and controls represent actions that can be taken in a given state. -/

class StateCtrl where
  State : Nat → Type
  Ctrl  : State t → Type

/-- Sequential decision problems given a value type V and Monad m. -/

class SDP (V : Type) (m : Type → Type) [Value V] [Monad m] extends StateCtrl where
  -- The next state(s) given the current state and action.
  next  : (s : State t) → Ctrl s → m (State (t + 1))
  -- The reward from taking an action that leads to a given state.
  reward : (s : State t) → Ctrl s → State (t + 1) → V
  -- A monotone aggregation function for values in the monad.
  measure : m V → V
  measure_comp_map_le_measure_comp_map :
    f ≤ g → measure ∘ (Functor.map f) ≤ measure ∘ (Functor.map g)
