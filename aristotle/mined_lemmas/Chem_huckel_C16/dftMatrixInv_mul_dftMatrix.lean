import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
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

namespace Chem

open Polynomial Matrix SimpleGraph

/-- The Hückel (adjacency) matrix of the cycle graph `C₁₆`, over `ℝ`. -/

lemma dftMatrixInv_mul_dftMatrix : dftMatrixInv * dftMatrix = 1 := by
  ext k l
  rw [Matrix.mul_apply]
  have key : ∀ j : Fin 16, dftMatrixInv k j * dftMatrix j l
      = (16 : ℂ)⁻¹ * (w ^ (15 * (k : ℕ) + (l : ℕ))) ^ (j : ℕ) := by
    intro j
    simp only [dftMatrixInv, dftMatrix, Matrix.of_apply]
    rw [← pow_mul, mul_assoc, ← pow_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  set z : ℂ := w ^ (15 * (k : ℕ) + (l : ℕ)) with hz
  by_cases h : k = l
  · subst h
    have h1 : z = 1 := by
      rw [hz]
      exact (w_primitive.pow_eq_one_iff_dvd _).2 ((dvd_iff_eq k k).2 rfl)
    simp [h1]
  · have hzne : z ≠ 1 := by
      rw [hz]
      exact w_pow_ne_one (fun hd => h ((dvd_iff_eq k l).1 hd))
    have hz16 : z ^ 16 = 1 := by
      rw [hz, ← pow_mul]
      exact (w_primitive.pow_eq_one_iff_dvd _).2 ⟨15 * (k : ℕ) + (l : ℕ), by ring⟩
    have hsum : ∑ j : Fin 16, z ^ (j : ℕ) = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun j => z ^ j) 16, geom_sum_eq hzne, hz16]
      simp
    rw [hsum]
    simp [h]

