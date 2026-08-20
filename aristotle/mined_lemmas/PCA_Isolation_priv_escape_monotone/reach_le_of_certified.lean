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

theorem reach_le_of_certified {pol : Policy} {avail : Caps} {bound p q : Nat}
    (hcert : Certified pol avail bound) (hp : p ≤ bound) (h : Reach pol avail p q) :
    q ≤ bound := by
  induction h with
  | refl => exact hp
  | tail _ hstep ih =>
      obtain ⟨d, hd, hreq, rfl⟩ := hstep
      have := hcert d hd (Nat.le_trans hreq ih)
      omega

/-- **Soundness.** A certified configuration admits no privilege escape. -/
