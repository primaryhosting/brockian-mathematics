import Mathlib

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

open Complex Polynomial Matrix

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma G_mul_F : G * F = 1 := by
  ext j m
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 18,
      G j k * F k m = (18 : ℂ)⁻¹ * ee ((k : ℕ) * (((m : ℕ) : ℤ) - ((j : ℕ) : ℤ))) := by
    intro k
    simp only [F, G, Matrix.of_apply]
    rw [show ((k : ℕ) : ℤ) * (((m : ℕ) : ℤ) - ((j : ℕ) : ℤ))
          = (-(((j : ℕ) : ℤ) * ((k : ℕ) : ℤ))) + ((k : ℕ) : ℤ) * ((m : ℕ) : ℤ) by ring, ee_add]
    ring
  simp only [hterm]
  rw [← Finset.mul_sum, ee_sum]
  rcases eq_or_ne j m with h | h
  · subst h; simp
  · rw [if_neg (fun hd => h (dvd_sub_iff_eq.mp hd).symm), Matrix.one_apply_ne h, mul_zero]

/-- The diagonal matrix of Hückel eigenvalues `2 cos (2πk/18)`. -/
