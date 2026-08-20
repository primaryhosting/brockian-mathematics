/-
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

/-- **Van der Waerden's theorem**: for any coloring `C : ℕ → κ` of the natural numbers by a
finite set of colors `κ`, and any length `k`, there is a monochromatic arithmetic progression
`a, a + d, a + 2d, …, a + (k-1)d` of length `k` with positive common difference `d`.

This is deduced from Mathlib's `Combinatorics.exists_mono_homothetic_copy` (a corollary of the
Hales–Jewett theorem) applied to the finite set `Finset.range k ⊆ ℕ`. -/
theorem van_der_waerden {κ : Type*} [Finite κ] (C : ℕ → κ) (k : ℕ) :
    ∃ a d : ℕ, 0 < d ∧ ∃ c : κ, ∀ i < k, C (a + i * d) = c := by
  obtain ⟨d, hd, b, c, h⟩ := Combinatorics.exists_mono_homothetic_copy (Finset.range k) C
  refine ⟨b, d, hd, c, fun i hi => ?_⟩
  have := h i (Finset.mem_range.mpr hi)
  rwa [smul_eq_mul, mul_comm, add_comm] at this

end Math2

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

