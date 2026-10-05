import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
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

namespace Frontier

open Finset
open scoped Matrix

/-! ## The Boolean hypercube -/

/-- Vertices of the `n`-dimensional Boolean hypercube. -/
abbrev Cube (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Flip the `i`-th coordinate of a hypercube vertex. -/

lemma huangMatrix_sq :
    huangMatrix n * huangMatrix n = (n : ℝ) • (1 : Matrix (Cube n) (Cube n) ℝ) := by
  ext x z
  rw [Matrix.mul_apply, huangMatrix_row_sum (fun y => huangMatrix n y z) x]
  by_cases hz : z = x
  · subst hz
    have hterm : ∀ i : Fin n, hsign z i * huangMatrix n (flipAt z i) z = 1 := by
      intro i
      rw [huangMatrix_flip_self, hsign_sq]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    simp
  · have hrew : ∑ i, hsign x i * huangMatrix n (flipAt x i) z
        = ∑ p : Fin n × Fin n,
            (if flipAt (flipAt x p.1) p.2 = z then hsign x p.1 * hsign (flipAt x p.1) p.2
              else 0) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [huangMatrix_apply_flip, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split <;> simp
    rw [hrew, huang_offdiag_sum x z hz]
    rw [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hz)]
    simp

