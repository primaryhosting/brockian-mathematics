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

lemma circulant_single_mul (a b : Fin 19) :
    Matrix.circulant (Pi.single a (1 : ℂ)) * Matrix.circulant (Pi.single b (1 : ℂ)) =
      Matrix.circulant (Pi.single (a + b) (1 : ℂ)) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (i - a)]
  · have h1 : i - (i - a) = a := by abel
    have hiff : (i - a - j = b) ↔ (i - j = a + b) := by
      constructor
      · intro h; rw [← h]; abel
      · intro h; rw [sub_right_comm, h]; abel
    simp only [Matrix.circulant_apply, h1, Pi.single_apply, if_true, one_mul]
    rw [if_congr hiff rfl rfl]
  · intro k _ hk
    have h0 : (if i - k = a then (1 : ℂ) else 0) = 0 := by
      apply if_neg
      intro h
      exact hk (by rw [← h]; abel)
    simp only [Matrix.circulant_apply, Pi.single_apply, h0, zero_mul]
  · simp

