import SDP.SDP
import SDP.Value.Rat
import SDP.Monad.SP
import SDP.Policy.FinEnum

/-- Has the green transition started? -/

inductive Transition : Type where
  /-- Transition Started -/
  | S : Transition
  /-- Transition Delayed -/
  | D : Transition

/-- Economic wealth -/

inductive Wealth : Type where
  /-- High wealth -/
  | H : Wealth
  /-- Low wealth -/
  | L : Wealth

/-- Is the world committed to severe climate change impacts -/

inductive Committment : Type where
  /-- The world is committed -/
  | C : Committment
  /-- The world is uncommitted -/
  | U : Committment

/-- States are 3-tuples of `Transition`, `Wealth` and `Committment` -/

abbrev State := Transition × Wealth × Committment

/-- When the transition has not yet started the controls are to either start
or delay further. -/

inductive StartDelay : Type where
  | Start : StartDelay
  | Delay : StartDelay
  deriving DecidableEq

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


def pTransition (tr : Transition) (c : Control' tr) : Nat × Nat :=
  match tr, c with
  | .S, _ => (1,0)
  | .D, .Start => (9,1)
  | .D, .Delay => (9,1)

def pWealth (tr : Transition) (w : Wealth) (c : Control' tr) : Nat × Nat :=
  match tr, w, c with
  | .D, .H, .Start => (3,7)
  | .D, .H, .Delay => (7,3)
  | .D, .L, .Start => (1,9)
  | .D, .L, .Delay => (3,7)
  | .S, .H, _      => (7,3)
  | .S, .L, _      => (3,7)

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
    SP.mkSP (
    (pS * pH * pC, (.S, .H, .C)) ::
    (pS * pH * pU, (.S, .H, .U)) ::
    (pS * pL * pC, (.S, .L, .C)) ::
    (pS * pL * pU, (.S, .L, .U)) ::
    (pD * pH * pC, (.D, .H, .C)) ::
    (pD * pH * pU, (.D, .H, .U)) ::
    (pD * pL * pC, (.D, .L, .C)) ::
    (pD * pL * pU, (.D, .L, .U)) ::
    [])

/-- The reward function. States where the world is committed or have low
wealth are bad. Other states are good. -/

def reward : State → Rat
  | (_ , .L, _) => 0
  | (_ , _, .C) => 0
  | (_ , .H, .U) => 1

/-- The Greenhouse gas emissions SDP -/

instance GHG_SDP : SDP Rat SP where
  State _ := State
  Ctrl := Control
  next {t} s c := next t s c
  reward _ _ s' := reward s'

/-- The optimal policy sequence for the SDP -/

def GHG_policySeq (t n : Nat) : PolicySeq t n :=
  FinEnum.bestPolicySeq FinEnum_Control Nonempty_Control t n
