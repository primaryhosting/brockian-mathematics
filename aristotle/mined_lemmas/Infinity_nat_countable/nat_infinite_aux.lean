import Mathlib

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

import Mathlib
/-!
# Nat Countable
Category: Frontier — Set Theory
Target: Infinity.nat_countable
Verification: verified (axiom-clean: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including module
-- docstrings, so the header block above sits immediately after the single `import Mathlib`.

namespace Infinity

/-- `ℕ` is countable: the identity map is an injection of `ℕ` into `ℕ`. -/

theorem nat_infinite_aux : Infinite ℕ := by
  refine ⟨fun h => ?_⟩
  have F := Fintype.ofFinite ℕ
  have hle : id (F.elems.sup id + 1) ≤ F.elems.sup id :=
    Finset.le_sup (f := id) (F.complete (F.elems.sup id + 1))
  simp only [id] at hle
  omega

/-- The naturals are countably infinite: `ℕ` is both a countable type and an infinite type. -/
