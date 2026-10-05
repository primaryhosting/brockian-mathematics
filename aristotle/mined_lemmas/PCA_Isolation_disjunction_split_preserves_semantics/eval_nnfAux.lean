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

theorem eval_nnfAux (s : State) (p : Policy) :
    ∀ b : Bool, eval s (nnfAux b p) = (if b then !(eval s p) else eval s p) := by
  induction p with
  | tt => intro b; cases b <;> simp [nnfAux]
  | ff => intro b; cases b <;> simp [nnfAux]
  | atom c => intro b; cases b <;> simp [nnfAux]
  | neg p ih => intro b; cases b <;> simp [nnfAux, ih]
  | and p q ihp ihq => intro b; cases b <;> simp [nnfAux, ihp, ihq]
  | or p q ihp ihq => intro b; cases b <;> simp [nnfAux, ihp, ihq]

/-- Negation normal form preserves the semantics. -/
