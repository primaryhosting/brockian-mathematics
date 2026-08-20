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

set_option grind.warning false

namespace Math2

/-- **Van der Waerden's theorem**: for any coloring `C : ℕ → κ` of the natural numbers by a
finite set of colors `κ`, and any length `k`, there is a monochromatic arithmetic progression
`a, a + d, a + 2d, …, a + (k-1)d` of length `k` with positive common difference `d`.

The proof is a direct consequence of Mathlib's `Combinatorics.exists_mono_homothetic_copy`
(a homothetic-copy form of van der Waerden's theorem for commutative monoids), which is in turn
derived from the Hales–Jewett theorem
(`Combinatorics.Line.exists_mono_in_high_dimension`). -/
theorem van_der_waerden {κ : Type*} [Finite κ] (C : ℕ → κ) (k : ℕ) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, C (a + i * d) = C a := by
  obtain ⟨d, hd, b, col, hcol⟩ :=
    Combinatorics.exists_mono_homothetic_copy (Finset.range k) C
  refine ⟨b, d, hd, fun i hi => ?_⟩
  have h1 : C (d • i + b) = col := hcol i (Finset.mem_range.mpr hi)
  have h0 : C (d • 0 + b) = col := hcol 0 (Finset.mem_range.mpr (by omega))
  have e1 : d • i + b = b + i * d := by simp only [smul_eq_mul]; ring
  have e0 : d • (0 : ℕ) + b = b := by simp
  rw [e1] at h1
  rw [e0] at h0
  rw [h1, h0]

end Math2

