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

theorem Reach.simulate {pol : Policy} {avail avail' : Caps} {p q p' : Nat}
    (h : Reach pol avail p q) (hav : avail ⊆ avail') (hp : p ≤ p') :
    ∃ q', Reach pol avail' p' q' ∧ q ≤ q' := by
  induction h with
  | refl => exact ⟨p', Reach.refl p', hp⟩
  | tail _ hstep ih =>
      obtain ⟨b', hb', hbb'⟩ := ih
      obtain ⟨c', hstep', hcc'⟩ := hstep.simulate hav hbb'
      exact ⟨c', hb'.tail hstep', hcc'⟩

/-! ## The main monotonicity theorem -/

/-- **Privilege escape is monotone.**

If an app can escape the isolation boundary `bound` starting from privilege `p` using the
capabilities in `avail`, then it can also escape any tighter boundary `bound' ≤ bound`
starting from any higher privilege `p' ≥ p` with any larger capability set `avail' ⊇ avail`.

Equivalently: escape is upward closed in the attacker's starting resources and downward
closed in the strength of the isolation boundary.  Contrapositively, isolation proved for a
configuration transfers to every weaker attacker and every wider boundary. -/
