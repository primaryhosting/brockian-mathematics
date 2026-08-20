/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency eigenvalues of the cycle graph `C n` (for `n ≥ 3`) are exactly
`2 cos (2πk/n)`, `k = 0, …, n-1`; these are the Hückel π-electron energies
(in units of the resonance integral `β`, measured from the Coulomb integral `α`).

The proof diagonalises the adjacency matrix by the discrete Fourier matrix
`F j k = ζ^(jk)` with `ζ = exp(2πi/n)`, and then uses `spectrum_diagonal`
(Mathlib, `Mathlib/LinearAlgebra/Eigenspace/Matrix.lean`) together with
`spectrum.units_conjugate`.
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- The primitive `n`-th root of unity `exp(2πi/n)`. -/

lemma sum_zeta_pow {n : ℕ} (hn : n ≠ 0) (j l : Fin n) :
    ∑ k : Fin n, zeta n ^ ((j : ℕ) * (k : ℕ)) * (zeta n)⁻¹ ^ ((k : ℕ) * (l : ℕ))
      = if j = l then (n : ℂ) else 0 := by
  set x : ℂ := zeta n ^ (j : ℕ) * (zeta n)⁻¹ ^ (l : ℕ) with hx
  have hterm : ∀ k : Fin n,
      zeta n ^ ((j : ℕ) * (k : ℕ)) * (zeta n)⁻¹ ^ ((k : ℕ) * (l : ℕ)) = x ^ (k : ℕ) := by
    intro k
    rw [hx, mul_pow, ← pow_mul, ← pow_mul, mul_comm (l : ℕ) (k : ℕ)]
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  have hxn : x ^ n = 1 := by
    rw [hx, mul_pow, ← pow_mul, ← pow_mul, mul_comm (j : ℕ) n, mul_comm (l : ℕ) n,
      pow_mul, pow_mul, zeta_pow_self hn, inv_pow, zeta_pow_self hn]
    simp
  by_cases hjl : j = l
  · subst hjl
    have hx1 : x = 1 := by
      rw [hx, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (zeta_ne_zero n))]
    simp [hx1]
  · have hx1 : x ≠ 1 := by
      intro h
      refine hjl (zeta_pow_inj hn ?_)
      rw [hx, inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ (zeta_ne_zero n))] at h
      exact h
    rw [Fin.sum_univ_eq_sum_range (fun i => x ^ i) n, geom_sum_eq hx1, hxn]
    simp [hjl]

