import SDP.Value
import Mathlib.Data.Real.Basic

namespace Real

noncomputable instance value : Value Real where
  add_le_add := add_le_add
  dec := decidableLT
