import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₈`; this is the Hückel matrix of
cyclooctatetraene in the units where the Coulomb integral is `0` and the resonance
integral is `1`. -/

lemma C8Adj_annihilating : C8Adj ^ 5 - (6 : ℂ) • C8Adj ^ 3 + (8 : ℂ) • C8Adj = 0 := by
  have hnum : ∀ (c : ℂ) (M : Matrix (Fin 8) (Fin 8) ℂ), c • M = (algebraMap ℂ _ c) * M := by
    intro c M
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have key : ((X + X ^ 7) ^ 5 - 6 * (X + X ^ 7) ^ 3 + 8 * (X + X ^ 7) : ℂ[X]) = (X ^ 8 - 1) *
      (-8 * X + 6 * X ^ 3 - X ^ 5 - 8 * X ^ 7 + 10 * X ^ 9 + X ^ 11 - X ^ 13 + 10 * X ^ 15
        + X ^ 19 + 5 * X ^ 21 + X ^ 27) := by
    ring
  have h2 := congrArg (Polynomial.aeval shift) key
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, map_neg,
    Polynomial.aeval_X] at h2
  rw [shift_pow_eight, sub_self, zero_mul] at h2
  rw [C8Adj_eq, hnum, hnum, map_ofNat, map_ofNat]
  exact h2

/-- Membership in the spectrum of a matrix is exactly the existence of an eigenvector. -/
