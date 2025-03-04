
import SDP.Value

class SDP where
  -- The monad of the SDP
  m : Type → Type
  monad : Monad m
  lawfulMonad : LawfulMonad m

  -- States
  State : Nat → Type
  -- Controls, actions that can be taken in a given state
  Ctrl  : State t → Type

  -- Computing the next possible states
  next : (s : State t) → Ctrl s → m (State (t + 1))

  -- The value type of the SDP
  V : Type
  value : Value V

  -- The reward function
  -- Represents the "score" received from taking a given action at a
  -- certain state that leads to a (another) certain state
  reward : (s : State t) → Ctrl s → State (t + 1) → V

  -- A monotone aggregation function for values in the monad
  measure : m V → V
  measure_comp_map_le_measure_comp_map :
    f ≤ g → measure ∘ (Functor.map f) ≤ measure ∘ (Functor.map g)
