/-!
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean 4 does not permit any command (including a module docstring) to precede
the `import` block, so in order for this file to *begin* with the header comment above it is
kept import-free.  Everything below is therefore developed from scratch on top of core Lean 4
(the file compiles unchanged inside this Mathlib project, and uses no axioms beyond
`propext`, `Classical.choice`, `Quot.sound`).
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA
namespace Isolation

/-! ## The isolation engine's model

Privilege levels are natural numbers, higher meaning more privileged.  An app runs inside an
isolation boundary `bound : Nat` and holds a set `avail` of capabilities.  Exercising a
capability requires a privilege level and confers one. -/

/-- A set of capabilities, represented as a predicate on capability names. -/

theorem certified_iff_no_escape {pol : Policy} {avail : Caps} {bound : Nat} :
    Certified pol avail bound ↔ ∀ p, p ≤ bound → ¬ Escapes pol avail bound p := by
  constructor
  · intro hcert p hp
    exact not_escapes_of_certified hcert hp
  · intro h
    exact Classical.byContradiction fun hcert =>
      h bound (Nat.le_refl bound) (escapes_of_not_certified hcert)

/-- Escape freedom is antitone in the attacker's resources: the contrapositive form of
`priv_escape_monotone`, which is how the isolation engine reuses proofs. -/
