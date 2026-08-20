/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-! -/` module docstring,
-- because in Lean 4.28 a module docstring is a command and cannot precede `import`.
-- The same text is repeated below as the module docstring.)

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel spectrum of the cyclic polyene C₁₉: the eigenvalues of the adjacency matrix of the
cycle graph `C₁₉` are exactly the numbers `2 cos (2πk/19)`, `k = 0, …, 18`.

The proof identifies the adjacency matrix with `S + S¹⁸`, where `S` is the cyclic shift matrix
(a circulant matrix), computes `spectrum ℂ S` (all 19-th roots of unity), and then applies the
spectral mapping theorem `spectrum.map_polynomial_aeval_of_degree_pos` for the polynomial
`X + X ^ 18`.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Chem

open Matrix Complex Polynomial SimpleGraph

/-- A primitive 19-th root of unity. -/

lemma mem_spectrum_of_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (μ : ℂ) (v : n → ℂ) (hv : v ≠ 0) (h : M *ᵥ v = μ • v) :
    μ ∈ spectrum ℂ M := by
  rw [spectrum.mem_iff]
  intro hu
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu
  apply hu
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv, ?_⟩
  have hmul : (algebraMap ℂ (Matrix n n ℂ) μ - M) *ᵥ v = μ • v - M *ᵥ v := by
    rw [Matrix.sub_mulVec]
    congr 1
    rw [Matrix.algebraMap_eq_diagonal]
    ext i
    simp [Matrix.mulVec, Matrix.diagonal, dotProduct]
  rw [hmul, h, sub_self]

