import SDP.Value
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

namespace Nat

instance value : Value Nat where
  add_le_add := add_le_add
  dec := decLt
