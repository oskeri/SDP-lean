import SDP.Value
import Mathlib.Algebra.Order.Ring.Unbundled.Rat

namespace Rat

instance value : Value Rat where
  add_le_add := add_le_add
  dec := instDecidableLt
