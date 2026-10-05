import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
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

namespace Chem

open Matrix Complex

/-! ## The `n`-th root of unity and its basic arithmetic -/

section Roots

variable (n : ℕ) [NeZero n]

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma adj_mul_fourier (hn : 3 ≤ n) :
    ((SimpleGraph.cycleGraph n).adjMatrix ℂ) * fourierMat n = fourierMat n * huckelDiag n := by
  ext i k
  rw [Matrix.mul_apply, huckelDiag, Matrix.mul_diagonal]
  have hpt : ∀ j : Fin n, ((SimpleGraph.cycleGraph n).adjMatrix ℂ) i j * fourierMat n j k
      = (if j = i + 1 then fourierMat n j k else 0)
        + (if j = i - 1 then fourierMat n j k else 0) := by
    intro j
    rw [SimpleGraph.adjMatrix_apply]
    have hiff := cycle_adj_iff n hn i j
    have hne := succ_ne_pred n hn i
    by_cases h1 : j = i + 1
    · rw [if_pos (hiff.mpr (Or.inl h1)), if_pos h1, if_neg (by rw [h1]; exact hne), one_mul,
        add_zero]
    · by_cases h2 : j = i - 1
      · rw [if_pos (hiff.mpr (Or.inr h2)), if_pos h2, if_neg h1, one_mul, zero_add]
      · rw [if_neg (fun hc => (hiff.mp hc).elim h1 h2), if_neg h1, if_neg h2, zero_mul, add_zero]
  rw [Finset.sum_congr rfl fun j _ => hpt j, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ (i + 1) (fun j => fourierMat n j k),
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun j => fourierMat n j k)]
  rw [if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  rw [fourierMat_shift_add n (by omega) i k, fourierMat_shift_sub n (by omega) i k,
    ← mul_add, zeta_pow_add_inv k]

/-- The Fourier matrix, as a unit of the matrix algebra. -/
