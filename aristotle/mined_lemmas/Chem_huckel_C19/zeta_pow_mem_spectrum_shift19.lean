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

lemma zeta_pow_mem_spectrum_shift19 (k : ℕ) : zeta19 ^ k ∈ spectrum ℂ shift19 := by
  set μ : ℂ := zeta19 ^ k with hμ
  have hμ19 : μ ^ 19 = 1 := by
    rw [hμ, ← pow_mul, mul_comm, pow_mul, zeta19_pow_19, one_pow]
  refine mem_spectrum_of_mulVec shift19 μ (fun j => μ ^ (19 - j.val)) ?_ ?_
  · intro hv
    have h0 : μ ^ (19 - (0 : Fin 19).val) = 0 := congrFun hv 0
    rw [show (19 - (0 : Fin 19).val) = 19 from rfl, hμ19] at h0
    exact one_ne_zero h0
  · funext i
    rw [shift19_mulVec, Pi.smul_apply, smul_eq_mul]
    exact pow_shift_relation μ hμ19 i

