import SDP.Value
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

namespace Nat

/-!
# Natural number values

This file defines a `Value` instance for `Nat`.

-/

instance value : Value Nat where
  add_le_add := add_le_add
  dec := decLt
