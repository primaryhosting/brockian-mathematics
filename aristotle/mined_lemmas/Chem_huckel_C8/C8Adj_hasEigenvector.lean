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

lemma C8Adj_hasEigenvector (k : Fin 8) :
    ∃ v : Fin 8 → ℂ, v ≠ 0 ∧
      C8Adj *ᵥ v = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 8) : ℝ) : ℂ) • v := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 8 with ht
  set z : ℂ := Complex.exp ((t : ℂ) * Complex.I) with hz
  have hz8 : z ^ 8 = 1 := by
    rw [hz, ← Complex.exp_nat_mul]
    have h : (8 : ℕ) * ((t : ℂ) * Complex.I) = ((k : ℕ) : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [ht]; push_cast; ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hzne : z ≠ 0 := Complex.exp_ne_zero _
  have hzinv : z ^ 7 = Complex.exp (-((t : ℂ) * Complex.I)) := by
    have h1 : z * z ^ 7 = 1 := by rw [← pow_succ']; exact hz8
    have h2 : z * Complex.exp (-((t : ℂ) * Complex.I)) = 1 := by
      rw [hz, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    exact mul_left_cancel₀ hzne (h1.trans h2.symm)
  have hsum : z + z ^ 7 = ((2 * Real.cos t : ℝ) : ℂ) := by
    rw [hzinv, hz, Complex.exp_mul_I,
      show -((t : ℂ) * Complex.I) = (-(t : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    push_cast [Complex.ofReal_cos]
    ring
  have hmod : ∀ a : ℕ, z ^ a = z ^ (a % 8) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a 8]
    rw [pow_add, pow_mul, hz8, one_pow, one_mul]
  have hs1 : ∀ i : Fin 8, ((i - 1 : Fin 8) : ℕ) = (7 + (i : ℕ)) % 8 := by decide
  have hs2 : ∀ i : Fin 8, ((i + 1 : Fin 8) : ℕ) = (1 + (i : ℕ)) % 8 := by decide
  refine ⟨fun i => z ^ ((i : ℕ)), ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    simp at h0
  · funext i
    rw [C8Adj_eq, shift_pow_seven, Matrix.add_mulVec, Pi.add_apply, shift_mulVec, shiftInv_mulVec,
      Pi.smul_apply, smul_eq_mul, ← hsum, hs1 i, hs2 i, ← hmod, ← hmod, pow_add, pow_add]
    ring

/-- **Hückel theory for cyclooctatetraene (C₈).**
The spectrum of the adjacency matrix of the cycle graph `C₈` is exactly
`{2 cos (2πk/8) : k = 0, …, 7}`. -/
