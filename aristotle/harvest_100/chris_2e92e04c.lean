/-
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated verbatim as a module docstring below.)

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

set_option grind.warning false

namespace Math2

/-- **Van der Waerden's theorem**: for any coloring `C : ℕ → κ` of the natural numbers by a
finite set `κ` of colors and any length `k`, there is a monochromatic arithmetic progression
`a, a + d, ..., a + (k-1) * d` with common difference `d > 0`.

The proof is a direct application of Mathlib's
`Combinatorics.exists_mono_homothetic_copy` (a generalization of van der Waerden's theorem,
derived there from the Hales–Jewett theorem), applied to the monoid `ℕ` and the
finite set `S = Finset.range k`. -/
theorem van_der_waerden {κ : Type*} [Finite κ] (C : ℕ → κ) (k : ℕ) :
    ∃ a d : ℕ, 0 < d ∧ ∃ c : κ, ∀ i < k, C (a + i * d) = c := by
  obtain ⟨d, hd, b, c, hc⟩ := Combinatorics.exists_mono_homothetic_copy (Finset.range k) C
  refine ⟨b, d, hd, c, fun i hi => ?_⟩
  have := hc i (Finset.mem_range.mpr hi)
  simpa [smul_eq_mul, Nat.mul_comm, Nat.add_comm] using this

end Math2

