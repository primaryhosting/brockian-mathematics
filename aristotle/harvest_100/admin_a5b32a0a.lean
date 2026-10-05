-- Header (kept verbatim; Lean requires `import` before any module docstring, so the
-- required header block is reproduced as a plain comment here and as a module
-- docstring after the imports).
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

namespace Math2

/-- **Van der Waerden's theorem**: for any coloring `C` of the natural numbers by finitely
many colors and any length `k`, there is a monochromatic arithmetic progression of length `k`,
i.e. a starting point `a` and a positive common difference `d` such that all of
`a, a + d, …, a + (k-1) * d` receive the same color `c`. -/
theorem van_der_waerden {κ : Type*} [Finite κ] (C : ℕ → κ) (k : ℕ) :
    ∃ (a d : ℕ) (c : κ), 0 < d ∧ ∀ i < k, C (a + i * d) = c := by
  obtain ⟨d, hd, b, c, hc⟩ :=
    Combinatorics.exists_mono_homothetic_copy (Finset.range k) C
  refine ⟨b, d, c, hd, fun i hi => ?_⟩
  have := hc i (Finset.mem_range.mpr hi)
  simpa [smul_eq_mul, Nat.add_comm, Nat.mul_comm] using this

end Math2

