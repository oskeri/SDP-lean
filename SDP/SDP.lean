
import SDP.Value

/-!
# Sequential Decision Problems (SDP:s)

This file defines SDP:s

## References

- Nocola Botta et al., "Responsibility Under Uncertainty: Which Climate Decisions Matter Most?", Environmental Modeling & Assesment (2023), doi: 10.1007/s10666-022-09867-w
-/

/-- States and Controls. States are a representation of the system at
a given time and controls represent actions that can be taken in a given state. -/

class StateCtrl where
  /-- Time-dependent type of states. -/
  State : Nat → Type
  /-- The type of controls available at a given state. -/
  Ctrl  : State t → Type

namespace StateCtrl

/-- States and Controls which can be printed. -/

class ToStringStateCtrl (sc : StateCtrl) where
  toStringState : State t → String
  toStringCtrl {s : State t} : Ctrl s → String

end StateCtrl

/-- Sequential decision problems given a measurable `Value` type `V` at `Monad` `m`. -/

class SDP (V : Type) (m : Type → Type) [Monad m] [Measure V m] extends StateCtrl where
  /-- The next state(s) given the current state and action. -/
  next  : (s : State t) → Ctrl s → m (State (t + 1))
  /-- The reward from taking an action that leads to a given state. -/
  reward : (s : State t) → Ctrl s → State (t + 1) → V
