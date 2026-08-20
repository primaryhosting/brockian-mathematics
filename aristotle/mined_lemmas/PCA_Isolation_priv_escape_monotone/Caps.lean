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

def Caps.Subset (avail avail' : Caps) : Prop := ∀ c, c ∈ avail → c ∈ avail'

instance : HasSubset Caps := ⟨Caps.Subset⟩

/-- An isolation policy for a proof-carrying app.

`req c` is the privilege level required to exercise capability `c`, and `gain c` is the
privilege level that exercising `c` confers. -/
structure Policy where
  /-- Privilege required to exercise a capability. -/
  req : Nat → Nat
  /-- Privilege conferred by exercising a capability. -/
  gain : Nat → Nat

/-- One step of the isolation engine: from privilege `p`, an app holding some available
capability `c` whose requirement it meets may move to privilege `max p (gain c)`.
Privilege is never dropped by a step. -/
