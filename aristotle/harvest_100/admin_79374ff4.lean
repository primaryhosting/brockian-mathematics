import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix

namespace Chem

/-- The primitive 9-th root of unity `exp (2πi/9)`. -/
noncomputable def omega9 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)

lemma omega9_primitive : IsPrimitiveRoot omega9 9 :=
  Complex.isPrimitiveRoot_exp 9 (by norm_num)

lemma omega9_pow_nine : omega9 ^ 9 = 1 := omega9_primitive.pow_eq_one

lemma omega9_pow_nine_pow (k : ℕ) : (omega9 ^ k) ^ 9 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, omega9_pow_nine, one_pow]

/-- `ω^k + ω^{-k} = 2 cos (2πk/9)`. -/
lemma omega9_pow_add_inv (k : ℕ) :
    omega9 ^ k + (omega9 ^ k)⁻¹ = ((2 * Real.cos (2 * Real.pi * k / 9) : ℝ) : ℂ) := by
  have h : omega9 ^ k = Complex.exp ((2 * Real.pi * k / 9 : ℝ) * Complex.I) := by
    rw [omega9, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [h, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos, ← neg_mul]
  ring

/-- Multiplying a vector by the adjacency matrix of `C₉` sums the two cyclic neighbours. -/
lemma cycleGraph9_mulVec (v : Fin 9 → ℂ) (i : Fin 9) :
    ((cycleGraph 9).adjMatrix ℂ *ᵥ v) i = v (i - 1) + v (i + 1) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply,
    show (cycleGraph 9).neighborFinset i = {i - 1, i + 1} from cycleGraph_neighborFinset (n := 7),
    Finset.sum_pair (by revert i; decide)]

/-- If `W ^ 9 = 1` then `j ↦ W ^ j` satisfies the eigenvector recurrence with
eigenvalue `W + W ^ 8`. -/
lemma pow_vec_eigen (W : ℂ) (hW : W ^ 9 = 1) (i : Fin 9) :
    W ^ ((i - 1 : Fin 9) : ℕ) + W ^ ((i + 1 : Fin 9) : ℕ) = (W + W ^ 8) * W ^ (i : ℕ) := by
  fin_cases i
  · show W ^ (8 : ℕ) + W ^ (1 : ℕ) = (W + W ^ 8) * W ^ (0 : ℕ); ring
  · show W ^ (0 : ℕ) + W ^ (2 : ℕ) = (W + W ^ 8) * W ^ (1 : ℕ); linear_combination -hW
  · show W ^ (1 : ℕ) + W ^ (3 : ℕ) = (W + W ^ 8) * W ^ (2 : ℕ); linear_combination -W * hW
  · show W ^ (2 : ℕ) + W ^ (4 : ℕ) = (W + W ^ 8) * W ^ (3 : ℕ); linear_combination -W ^ 2 * hW
  · show W ^ (3 : ℕ) + W ^ (5 : ℕ) = (W + W ^ 8) * W ^ (4 : ℕ); linear_combination -W ^ 3 * hW
  · show W ^ (4 : ℕ) + W ^ (6 : ℕ) = (W + W ^ 8) * W ^ (5 : ℕ); linear_combination -W ^ 4 * hW
  · show W ^ (5 : ℕ) + W ^ (7 : ℕ) = (W + W ^ 8) * W ^ (6 : ℕ); linear_combination -W ^ 5 * hW
  · show W ^ (6 : ℕ) + W ^ (8 : ℕ) = (W + W ^ 8) * W ^ (7 : ℕ); linear_combination -W ^ 6 * hW
  · show W ^ (7 : ℕ) + W ^ (0 : ℕ) = (W + W ^ 8) * W ^ (8 : ℕ)
    linear_combination (-(1 + W ^ 7)) * hW

/-- Every complex number is of the form `z + z⁻¹` for some nonzero `z`. -/
lemma exists_ne_zero_sq_add_one (μ : ℂ) : ∃ z : ℂ, z ≠ 0 ∧ z ^ 2 + 1 = μ * z := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (n := 2) (μ ^ 2 - 4) (by norm_num)
  have key : ((μ + s) / 2) ^ 2 + 1 = μ * ((μ + s) / 2) := by field_simp; linear_combination hs
  refine ⟨(μ + s) / 2, ?_, key⟩
  intro h
  rw [h] at key
  simp at key

/-- Every eigenvalue of `C₉` comes from a 9-th root of unity. -/
lemma root_of_unity_of_eigen {v : Fin 9 → ℂ} {μ z : ℂ} (hv0 : v ≠ 0)
    (hv : ∀ i : Fin 9, v (i - 1) + v (i + 1) = μ * v i) (hz : z ≠ 0) (hz2 : z ^ 2 + 1 = μ * z) :
    z ^ 9 = 1 := by
  have e0 : v 8 + v 1 = μ * v 0 := by simpa using hv 0
  have e1 : v 0 + v 2 = μ * v 1 := by simpa using hv 1
  have e2 : v 1 + v 3 = μ * v 2 := by simpa using hv 2
  have e3 : v 2 + v 4 = μ * v 3 := by simpa using hv 3
  have e4 : v 3 + v 5 = μ * v 4 := by simpa using hv 4
  have e5 : v 4 + v 6 = μ * v 5 := by simpa using hv 5
  have e6 : v 5 + v 7 = μ * v 6 := by simpa using hv 6
  have e7 : v 6 + v 8 = μ * v 7 := by simpa using hv 7
  have e8 : v 7 + v 0 = μ * v 8 := by simpa using hv 8
  -- the "shifted" quantities `u i = v (i+1) - z * v i` satisfy `u i = z * u (i+1)`
  have h0 : v 1 - z * v 0 = z * (v 2 - z * v 1) := by linear_combination (-z) * e1 + v 1 * hz2
  have h1 : v 2 - z * v 1 = z * (v 3 - z * v 2) := by linear_combination (-z) * e2 + v 2 * hz2
  have h2 : v 3 - z * v 2 = z * (v 4 - z * v 3) := by linear_combination (-z) * e3 + v 3 * hz2
  have h3 : v 4 - z * v 3 = z * (v 5 - z * v 4) := by linear_combination (-z) * e4 + v 4 * hz2
  have h4 : v 5 - z * v 4 = z * (v 6 - z * v 5) := by linear_combination (-z) * e5 + v 5 * hz2
  have h5 : v 6 - z * v 5 = z * (v 7 - z * v 6) := by linear_combination (-z) * e6 + v 6 * hz2
  have h6 : v 7 - z * v 6 = z * (v 8 - z * v 7) := by linear_combination (-z) * e7 + v 7 * hz2
  have h7 : v 8 - z * v 7 = z * (v 0 - z * v 8) := by linear_combination (-z) * e8 + v 8 * hz2
  have h8 : v 0 - z * v 8 = z * (v 1 - z * v 0) := by linear_combination (-z) * e0 + v 0 * hz2
  by_contra hne
  -- if `z ^ 9 ≠ 1` all the `u i` vanish
  have hcycle : v 1 - z * v 0 = z ^ 9 * (v 1 - z * v 0) := by
    linear_combination h0 + z * h1 + z ^ 2 * h2 + z ^ 3 * h3 + z ^ 4 * h4 + z ^ 5 * h5 +
      z ^ 6 * h6 + z ^ 7 * h7 + z ^ 8 * h8
  have hu0 : v 1 - z * v 0 = 0 := by
    have : (z ^ 9 - 1) * (v 1 - z * v 0) = 0 := by linear_combination -hcycle
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  have hu1 : v 2 - z * v 1 = 0 := by
    have := h0; rw [hu0] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  have hu2 : v 3 - z * v 2 = 0 := by
    have := h1; rw [hu1] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  have hu3 : v 4 - z * v 3 = 0 := by
    have := h2; rw [hu2] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  have hu4 : v 5 - z * v 4 = 0 := by
    have := h3; rw [hu3] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  have hu5 : v 6 - z * v 5 = 0 := by
    have := h4; rw [hu4] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  have hu6 : v 7 - z * v 6 = 0 := by
    have := h5; rw [hu5] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  have hu7 : v 8 - z * v 7 = 0 := by
    have := h6; rw [hu6] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  have hu8 : v 0 - z * v 8 = 0 := by
    have := h7; rw [hu7] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  -- hence `v 0 = z ^ 9 * v 0`, forcing `v = 0`
  have hv00 : v 0 = 0 := by
    have hcyc : v 0 = z ^ 9 * v 0 := by
      have := sub_eq_zero.1 hu8
      linear_combination this + z * sub_eq_zero.1 hu7 + z ^ 2 * sub_eq_zero.1 hu6 +
        z ^ 3 * sub_eq_zero.1 hu5 + z ^ 4 * sub_eq_zero.1 hu4 + z ^ 5 * sub_eq_zero.1 hu3 +
        z ^ 6 * sub_eq_zero.1 hu2 + z ^ 7 * sub_eq_zero.1 hu1 + z ^ 8 * sub_eq_zero.1 hu0
    have : (z ^ 9 - 1) * v 0 = 0 := by linear_combination -hcyc
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  apply hv0
  funext i
  have h1' : v 1 = 0 := by have := sub_eq_zero.1 hu0; rw [this, hv00, mul_zero]
  have h2' : v 2 = 0 := by have := sub_eq_zero.1 hu1; rw [this, h1', mul_zero]
  have h3' : v 3 = 0 := by have := sub_eq_zero.1 hu2; rw [this, h2', mul_zero]
  have h4' : v 4 = 0 := by have := sub_eq_zero.1 hu3; rw [this, h3', mul_zero]
  have h5' : v 5 = 0 := by have := sub_eq_zero.1 hu4; rw [this, h4', mul_zero]
  have h6' : v 6 = 0 := by have := sub_eq_zero.1 hu5; rw [this, h5', mul_zero]
  have h7' : v 7 = 0 := by have := sub_eq_zero.1 hu6; rw [this, h6', mul_zero]
  have h8' : v 8 = 0 := by have := sub_eq_zero.1 hu7; rw [this, h7', mul_zero]
  fin_cases i <;> simp_all

/-- **Hückel theory for the C₉ ring.**  A complex number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₉` if and only if `μ = 2 cos (2πk/9)` for some `k = 0, …, 8`. -/
theorem huckel_C9 (μ : ℂ) :
    (∃ v : Fin 9 → ℂ, v ≠ 0 ∧ (cycleGraph 9).adjMatrix ℂ *ᵥ v = μ • v) ↔
      ∃ k : Fin 9, μ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 9) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    have hrec : ∀ i : Fin 9, v (i - 1) + v (i + 1) = μ * v i := by
      intro i
      rw [← cycleGraph9_mulVec v i, hv]
      simp
    obtain ⟨z, hzne, key⟩ := exists_ne_zero_sq_add_one μ
    have hz9 : z ^ 9 = 1 := root_of_unity_of_eigen hv0 hrec hzne key
    obtain ⟨k, hk, hkeq⟩ := omega9_primitive.eq_pow_of_pow_eq_one hz9
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [← omega9_pow_add_inv k, hkeq]
    field_simp
    linear_combination -key
  · rintro ⟨k, rfl⟩
    set W : ℂ := omega9 ^ (k : ℕ) with hWdef
    have hW : W ^ 9 = 1 := omega9_pow_nine_pow _
    have hWinv : (W : ℂ)⁻¹ = W ^ 8 :=
      inv_eq_of_mul_eq_one_left (by linear_combination hW)
    have hμ : ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 9) : ℝ) : ℂ) = W + W ^ 8 := by
      rw [← omega9_pow_add_inv (k : ℕ), ← hWdef, hWinv]
    refine ⟨fun j => W ^ (j : ℕ), ?_, ?_⟩
    · intro h
      have h0 : (fun j : Fin 9 => W ^ (j : ℕ)) 0 = 0 := by rw [h]; rfl
      simp at h0
    · funext i
      rw [cycleGraph9_mulVec]
      simp only [Pi.smul_apply, smul_eq_mul, hμ]
      exact pow_vec_eigen W hW i

end Chem

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

