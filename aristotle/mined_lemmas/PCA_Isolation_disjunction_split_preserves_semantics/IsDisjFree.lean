/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

/-! ## Policies

The isolation engine of a proof-carrying application reasons about *isolation
policies*: propositional constraints over atomic capabilities (permissions,
resource handles, ...).  A *state* of the machine is an assignment of a Boolean
truth value to every capability. -/

/-- Atomic capabilities are indexed by natural numbers. -/
abbrev Cap := Nat

/-- A machine state: which capabilities are currently granted. -/
abbrev State := Cap → Bool

/-- Isolation policies. -/
inductive Policy where
  | tt : Policy
  | ff : Policy
  | atom : Cap → Policy
  | neg : Policy → Policy
  | and : Policy → Policy → Policy
  | or : Policy → Policy → Policy
  deriving DecidableEq, Repr

namespace Policy

/-- Boolean semantics of a policy in a state. -/

def IsDisjFree : Policy → Bool
  | tt => true
  | ff => true
  | atom _ => true
  | neg _ => true
  | and p q => IsDisjFree p && IsDisjFree q
  | or _ _ => false

/-- A *cube*: a conjunction of literals. -/
