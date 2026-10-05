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

def nnfAux : Bool → Policy → Policy
  | false, tt => tt
  | true, tt => ff
  | false, ff => ff
  | true, ff => tt
  | false, atom c => atom c
  | true, atom c => neg (atom c)
  | b, neg p => nnfAux (!b) p
  | false, and p q => and (nnfAux false p) (nnfAux false q)
  | true, and p q => or (nnfAux true p) (nnfAux true q)
  | false, or p q => or (nnfAux false p) (nnfAux false q)
  | true, or p q => and (nnfAux true p) (nnfAux true q)

/-- Negation normal form of a policy. -/
