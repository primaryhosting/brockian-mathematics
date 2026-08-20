/-
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4.28 rejects a `/-!` module docstring before `import`, so the header
-- above is a plain block comment; it is repeated verbatim as a module docstring
-- immediately after the imports.)
import RequestProject.Ramsey

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- A finite set of natural numbers is *relatively large* (in the sense of
Paris–Harrington) if it is nonempty and its cardinality is at least its least
element. -/

theorem isLarge_iff_min' {H : Finset ℕ} (h : H.Nonempty) :
    IsLarge H ↔ H.min' h ≤ H.card := by
  constructor
  · rintro ⟨a, haH, -, hcard⟩
    exact le_trans (H.min'_le a haH) hcard
  · intro hle
    exact ⟨H.min' h, H.min'_mem h, fun b hb => H.min'_le b hb, hle⟩

/-- `IsHomogeneous n c H` says that the colouring `c` of `n`-element sets takes the
same value on all `n`-element subsets of the finite set `H`. -/
