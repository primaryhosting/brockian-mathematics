/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Finset

namespace Chem

/-! ### The cyclic shift operator -/

/-- The cyclic shift endomorphism of `Fin 13 → ℂ`, `f ↦ (i ↦ f (i + 1))`. -/

lemma aeval_cycA_qpoly : (Polynomial.aeval cycA) qpoly = 0 := by
  have hcyc : (Polynomial.aeval shift) (X + X ^ 12 : ℂ[X]) = cycA := by
    simp [cycA]
  obtain ⟨r, hr⟩ := dvd_qpoly_comp
  have h1 : (Polynomial.aeval shift) (qpoly.comp (X + X ^ 12)) = 0 := by
    rw [hr, map_mul, map_sub, map_pow, map_one, Polynomial.aeval_X, shift_pow_thirteen,
      sub_self, zero_mul]
  rwa [Polynomial.aeval_comp, hcyc] at h1

/-! ### Main theorem -/

/-- **Hückel theory for C₁₃.** A complex number `μ` is an eigenvalue of the adjacency matrix
of the cycle graph `C₁₃` if and only if `μ = 2 cos (2πk/13)` for some `k ∈ {0, …, 12}`. -/
