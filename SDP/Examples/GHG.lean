import SDP.SDP
import SDP.Value.Rat
import SDP.Monad.SP
import SDP.Policy.FinEnum
import SDP.Trajectory

/-!
# Greenhouse gas emissions

This example is taken from the paper "Responsibility Under Uncertainty:
Which Climate Decisions Matter Most?" by Botta et al.

It is a simple model of
the problem of when to start a green energy transition. The world is modelled
as a 3-tuple of whether green transition has started, the economic wealth and
whether the world is committed to severe climate change impacts. The only decision
is to either start the green transition or not (once started there is no more
decision to take).

Note that the results do not quite match the ones presented in the paper. There is
likely an error in the transition function `next`.

-/

open StateCtrl

namespace GHG

/-- Has the green transition started? -/

inductive Transition : Type where
  /-- Transition Started -/
  | S : Transition
  /-- Transition Delayed -/
  | D : Transition

/-- `ToString` instance for `Transition`. -/

instance instToStringTransition : ToString Transition where
  toString
    | .S => "S"
    | .D => "D"

/-- Economic wealth -/

inductive Wealth : Type where
  /-- High wealth -/
  | H : Wealth
  /-- Low wealth -/
  | L : Wealth

/-- `ToString` instance for `Wealth`. -/

instance instToStringWealth : ToString Wealth where
  toString
    | .H => "H"
    | .L => "L"

/-- Is the world committed to severe climate change impacts -/

inductive Committment : Type where
  /-- The world is committed -/
  | C : Committment
  /-- The world is uncommitted -/
  | U : Committment

/-- `ToString` instance for `Committment`. -/

instance instToStringCommittment : ToString Committment where
  toString
    | .C => "C"
    | .U => "U"

/-- States are 3-tuples of `Transition`, `Wealth` and `Committment` -/

abbrev State := Transition × Wealth × Committment

/-- `ToString` instance for `State` -/

instance instToStringState : ToString State where
  toString
    | (t, w, c) => toString t ++ toString w ++ toString c

/-- When the transition has not yet started the controls are to either start
or delay further. -/

inductive StartDelay : Type where
  | Start : StartDelay
  | Delay : StartDelay
  deriving DecidableEq

/-- `ToString` instance for `StartDelay`. -/

instance instToStringStartDelay : ToString StartDelay where
  toString
    | .Start => "Start"
    | .Delay => "Delay"

/-- When the transition has started, there is only one control. -/

def Control' : Transition → Type
  | .S => Unit
  | .D => StartDelay

/-- A variant of `Control'` dependent on `State` instead of `Transition`. -/

def Control (s : State) : Type := Control' s.1

/-- The type `StartDelay` is finitely enumerable. -/

instance FinEnum_StartDelay : FinEnum StartDelay :=
  FinEnum.ofList [.Start, .Delay]
    (fun x => by cases x <;> trivial)

/-- The type `Control` is finitely enumerable. -/

instance FinEnum_Control (s : State) : FinEnum (Control s) :=
  match s with
  | (.S, _) => FinEnum.punit
  | (.D, _) => FinEnum_StartDelay

/-- The type `Control` is nonempty. -/

instance Nonempty_Control (s : State) : Nonempty (Control s) :=
  match s with
  | (.S, _) => .intro ()
  | (.D, _) => .intro .Start

/-- `ToString` instance for `Control`. -/

instance instToStringControl (s : State) : ToString (Control s) :=
  match s with
  | (.S, _) => { toString _ := "     " }
  | (.D, _) => instToStringStartDelay

/-- The probabilities of transitioning to `S` or `D` states from a given
`Control'`. -/

def pTransition (tr : Transition) (c : Control' tr) : Nat × Nat :=
  match tr, c with
  | .S, _ => (1,0)
  | .D, .Start => (9,1)
  | .D, .Delay => (1,9)

/-- The probabilities of transitioning to `H` or `L` states from a given
`Control'`. -/

def pWealth (tr : Transition) (w : Wealth) (c : Control' tr) : Nat × Nat :=
  match tr, w, c with
  | .D, .H, .Start => (3,7)
  | .D, .H, .Delay => (7,3)
  | .D, .L, .Start => (1,9)
  | .D, .L, .Delay => (3,7)
  | .S, .H, _      => (7,3)
  | .S, .L, _      => (3,7)

/-- The probabilities of transitioning to `C` or `U` states from a given
`Control'`. -/

def pCommittment (t : Nat) (tr : Transition) (c : Committment) (ctrl : Control' tr) : Nat × Nat :=
  match t, tr, c, ctrl with
  | _ , _ , .C , _ => (1,0)
  | .zero, .D, .U, .Start => (1,9)
  | .zero, .D, .U, .Delay => (3,7)
  | .zero, .S, .U, _ => (1,9)
  | .succ _, .D, .U, .Start => (1,9)
  | .succ _, .D, .U, .Delay => (7,3)
  | .succ _, .S, .U, _ => (1,9)

/-- The transition function -/

def next (t : Nat) (s : State) (ctrl : Control s) : SP State :=
  match s with
  | (tr, w, c) =>
    have (pS, pD) := pTransition tr ctrl
    have (pH, pL) := pWealth tr w ctrl
    have (pC, pU) := pCommittment t tr c ctrl
    SP.dropImpossible (SP.mkSP (
    (pS * pH * pC, (.S, .H, .C)) ::
    (pS * pH * pU, (.S, .H, .U)) ::
    (pS * pL * pC, (.S, .L, .C)) ::
    (pS * pL * pU, (.S, .L, .U)) ::
    (pD * pH * pC, (.D, .H, .C)) ::
    (pD * pH * pU, (.D, .H, .U)) ::
    (pD * pL * pC, (.D, .L, .C)) ::
    (pD * pL * pU, (.D, .L, .U)) ::
    []))

/-- The reward function. States where the world is committed or have low
wealth are bad. Other states are good. -/

def reward : State → Rat
  | (_ , _, .C) => 0
  | (_ , .L, _) => 0
  | (_ , .H, .U) => 1

/-- The Greenhouse gas emissions SDP -/

instance GHG_SDP : SDP Rat SP where
  State _ := State
  Ctrl := Control
  next {t} s c := next t s c
  reward _ _ s' := reward s'


/-- `ToStringStateCtrl` instance for the SDP -/

instance instToStringStateCtrl : ToStringStateCtrl GHG_SDP.toStateCtrl where
  toStringState := toString (self := instToStringState)
  toStringCtrl := toString (self := instToStringControl _)

/-- The optimal policy sequence for the SDP -/

def GHG_policySeq (t n : Nat) : PolicySeq t n :=
  FinEnum.bestPolicySeq FinEnum_Control Nonempty_Control t n

/-- The trajectory of the optimal sequence. -/

def GHG_trj (t n : Nat) (s : State) : SP (Trj t (n + 1)) :=
  Trj.trj (GHG_policySeq t n) s

/-- The value of the optimal sequence. -/

def GHG_val (t n : Nat) (s : State) : Rat :=
  PolicySeq.val (GHG_policySeq t n) s

-- Display the optimal trajectory
#eval GHG_trj 0 1 (.D,.H,.U)

-- Display the optimal value
#eval GHG_val 0 1 (.D,.H,.U)
