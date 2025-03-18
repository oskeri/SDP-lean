-- This module serves as the root of the `SDP` library.

-- Definition of the `Argmax` typeclass
import SDP.Util.Argmax
-- `Argmax` instance for nonempty, finitely enumerable types
import SDP.Util.FinEnum
-- Definition of total, decidable preorders.
import SDP.Util.Order

-- A monad instance
import SDP.Monad.SP

-- Definitions of Values and Values with a `measure` function-
import SDP.Value

-- `Value` and `Measure` instances
import SDP.Value.Nat
import SDP.Value.Nat.Max
import SDP.Value.Rat
import SDP.Value.Real

-- Definition of SDP:s
import SDP.SDP

-- Definition of policies, policy sequences and solving SDP:s
-- (finding optimal policy sequences) using backwards induction
import SDP.Policy
-- Solving SDP:s using an `argmax` function
import SDP.Policy.Argmax
-- Solving SDP:s for nonempty and finitely enumerable control spaces.
import SDP.Policy.FinEnum

-- Definition of Trajectories and displaying SDP solutions.
import SDP.Trajectory

-- Some examples
import SDP.Examples.GHG
import SDP.Examples.TicTacToe
