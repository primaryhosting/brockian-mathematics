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

theorem split_isCube_of_isNNF (p : Policy) (hp : IsNNF p = true) :
    ∀ b ∈ split p, IsCube b = true := by
  induction p with
  | tt => simp [split, IsCube, IsLiteral]
  | ff => simp [split, IsCube, IsLiteral]
  | atom c => simp [split, IsCube, IsLiteral]
  | neg p =>
      intro b hb
      simp only [split, List.mem_singleton] at hb
      subst hb
      cases p <;> simp_all [IsNNF, IsCube, IsLiteral]
  | or p q ihp ihq =>
      simp only [IsNNF, Bool.and_eq_true] at hp
      intro b hb
      rcases List.mem_append.mp hb with h | h
      · exact ihp hp.1 b h
      · exact ihq hp.2 b h
  | and p q ihp ihq =>
      simp only [IsNNF, Bool.and_eq_true] at hp
      intro b hb
      simp only [split, List.mem_flatMap, List.mem_map] at hb
      obtain ⟨a, ha, c, hc, rfl⟩ := hb
      simp [IsCube, ihp hp.1 a ha, ihq hp.2 c hc]

/-! ## The isolation pipeline -/

/-- The isolation engine: normalise, then split into isolated branches. -/
