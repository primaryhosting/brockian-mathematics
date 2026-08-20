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

theorem escapes_of_not_certified {pol : Policy} {avail : Caps} {bound : Nat}
    (hcert : ¬ Certified pol avail bound) :
    Escapes pol avail bound bound := by
  refine Classical.byContradiction (fun hesc => hcert ?_)
  intro c hc hreq
  refine Classical.byContradiction (fun hgain => hesc ?_)
  exact ⟨max bound (pol.gain c), Reach.single ⟨c, hc, hreq, rfl⟩, by omega⟩

/-- **Soundness and completeness of the isolation engine.**  The local certificate check
holds exactly when no app starting inside the isolation boundary can escape it. -/
