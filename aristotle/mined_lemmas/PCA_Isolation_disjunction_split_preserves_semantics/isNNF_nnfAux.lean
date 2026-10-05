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

theorem isNNF_nnfAux (p : Policy) : ∀ b : Bool, IsNNF (nnfAux b p) = true := by
  induction p with
  | tt => intro b; cases b <;> simp [nnfAux, IsNNF]
  | ff => intro b; cases b <;> simp [nnfAux, IsNNF]
  | atom c => intro b; cases b <;> simp [nnfAux, IsNNF]
  | neg p ih => intro b; cases b <;> simp [nnfAux, ih]
  | and p q ihp ihq => intro b; cases b <;> simp [nnfAux, IsNNF, ihp, ihq]
  | or p q ihp ihq => intro b; cases b <;> simp [nnfAux, IsNNF, ihp, ihq]

