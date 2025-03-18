import SDP.Value
import Mathlib.Data.Real.Basic

/-!
# Real number values

This file defines a value instance for `Real`.

Note that since decidability of the order relation is uncompuatble,
this instance is uncomputable.

-/

namespace Real

noncomputable instance value : Value Real where
  add_le_add := add_le_add
  dec := decidableLT
