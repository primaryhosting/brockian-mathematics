import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl,
in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/
def C3adj : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if i = j then 0 else 1

/-- `2 cos (2π·0/3) = 2`. -/
lemma C3_cos_zero : Real.cos (2 * Real.pi * (0 : ℝ) / 3) = 1 := by norm_num

/-- `2 cos (2π·1/3) = -1`. -/
lemma C3_cos_one : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  rw [show (2 * Real.pi / 3) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]

/-- `2 cos (2π·2/3) = -1`. -/
lemma C3_cos_two : Real.cos (2 * Real.pi * (2 : ℝ) / 3) = -(1 / 2) := by
  rw [show (2 * Real.pi * (2 : ℝ) / 3) = Real.pi + Real.pi / 3 by ring, Real.cos_add,
    Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
  ring

/-- The product of the linear factors `X - 2 cos (2πk/3)` is `(X - 2)(X + 1)²`. -/
lemma C3_prod_factors :
    ∏ k : Fin 3, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 3))) =
      (X - C 2) * (X + C 1) ^ 2 := by
  rw [Fin.prod_univ_three]
  norm_num [C3_cos_zero, C3_cos_one, C3_cos_two]
  ring

/-- The characteristic polynomial of the `C₃` adjacency matrix. -/
lemma C3_charpoly : C3adj.charpoly = (X - C 2) * (X + C 1) ^ 2 := by
  rw [Matrix.charpoly, Matrix.det_fin_three, C_ofNat 2, map_one]
  simp [C3adj]
  ring

/-- A real number is an eigenvalue of the `C₃` adjacency matrix iff it is `2` or `-1`. -/
lemma C3_eigenvalue_iff (μ : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔ (μ = 2 ∨ μ = -1) := by
  have key : (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ (C3adj - μ • 1).mulVec v = 0) ↔ (C3adj - μ • 1).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff
  have hre : ∀ v : Fin 3 → ℝ, (C3adj - μ • 1).mulVec v = 0 ↔ C3adj.mulVec v = μ • v := by
    intro v
    rw [Matrix.sub_mulVec, sub_eq_zero, smul_mulVec, Matrix.one_mulVec]
  simp only [hre] at key
  rw [key, Matrix.det_fin_three]
  simp [C3adj]
  constructor
  · intro h
    have h2 : (μ - 2) * (μ + 1) ^ 2 = 0 := by nlinarith [h]
    rcases mul_eq_zero.1 h2 with h1 | h1
    · left; linarith
    · right; nlinarith [sq_nonneg (μ + 1)]
  · rintro (rfl | rfl) <;> ring

/-! ### Complex Bloch (Hückel molecular orbital) eigenvectors -/

/-- The primitive cube root of unity `ω = exp(2πi/3)`. -/
noncomputable def omega3 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

lemma omega3_pow_three : omega3 ^ 3 = 1 := by
  rw [omega3, ← Complex.exp_nat_mul, show ((3 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 3)
    = 2 * Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma omega3_ne_one : omega3 ≠ 1 := by
  rw [omega3, Ne, Complex.exp_eq_one_iff]
  rintro ⟨n, hn⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp at hn
  have : (1 : ℤ) = 3 * n := by exact_mod_cast hn
  omega

lemma omega3_quad : omega3 ^ 2 + omega3 + 1 = 0 := by
  have h : (omega3 - 1) * (omega3 ^ 2 + omega3 + 1) = 0 := by linear_combination omega3_pow_three
  rcases mul_eq_zero.1 h with h1 | h1
  · exact absurd (by linear_combination h1 : omega3 = 1) omega3_ne_one
  · exact h1

lemma omega3_exp_one : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3) = omega3 := rfl

lemma omega3_exp_two : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * 2 / 3) = omega3 ^ 2 := by
  rw [omega3, ← Complex.exp_nat_mul]; ring_nf

lemma omega3_exp_four : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (2 * 2) / 3) = omega3 := by
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (2 * 2) / 3)
      = ((4 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 3) by push_cast; ring,
    Complex.exp_nat_mul, ← omega3]
  calc omega3 ^ 4 = omega3 ^ 3 * omega3 := by ring
    _ = omega3 := by rw [omega3_pow_three, one_mul]

/-- The adjacency matrix of `C₃`, viewed over `ℂ`. -/
def C3adjC : Matrix (Fin 3) (Fin 3) ℂ := fun i j => if i = j then 0 else 1

/-- The `k`-th Bloch (Hückel molecular orbital) vector of `C₃`,
with components `exp(2πi k j / 3)`. -/
noncomputable def blochMO (k : Fin 3) : Fin 3 → ℂ :=
  fun j => Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * (j : ℕ)) / 3)

/-- The Bloch vector `blochMO k` is nonzero. -/
lemma blochMO_ne_zero (k : Fin 3) : blochMO k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [blochMO] at h0

/-- The Bloch vector `blochMO k` is an eigenvector of the `C₃` adjacency matrix
with eigenvalue `2 cos (2πk/3)`. -/
lemma C3adjC_mulVec_blochMO (k : Fin 3) :
    C3adjC.mulVec (blochMO k)
      = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) : ℝ) : ℂ) • blochMO k := by
  funext j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, C3adjC, blochMO,
      C3_cos_one, C3_cos_two] <;>
    (try simp only [omega3_exp_one, omega3_exp_two, omega3_exp_four]) <;>
    first
      | linear_combination omega3_quad
      | linear_combination -omega3_quad
      | norm_num

/-- **Hückel theory for cyclopropenyl (`C₃`).**
The adjacency (Hückel) eigenvalues of the cycle graph `C₃` are exactly the numbers
`2 cos (2πk/3)` for `k = 0, 1, 2`:

* the characteristic polynomial factors as `∏ k, (X - 2 cos (2πk/3))`, so these are the
  eigenvalues counted with multiplicity (namely `2, -1, -1`);
* a real number `μ` admits a nonzero eigenvector iff `μ = 2 cos (2πk/3)` for some `k`;
* for each `k`, the Bloch vector `(exp(2πi k j/3))_j` is a nonzero eigenvector with
  eigenvalue `2 cos (2πk/3)`. -/
theorem huckel_C3 :
    C3adj.charpoly = ∏ k : Fin 3, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 3))) ∧
      (∀ μ : ℝ, (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔
        ∃ k : Fin 3, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 3)) ∧
      ∀ k : Fin 3, blochMO k ≠ 0 ∧
        C3adjC.mulVec (blochMO k)
          = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) : ℝ) : ℂ) • blochMO k := by
  refine ⟨by rw [C3_charpoly, C3_prod_factors], fun μ => ?_,
    fun k => ⟨blochMO_ne_zero k, C3adjC_mulVec_blochMO k⟩⟩
  rw [C3_eigenvalue_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num [C3_cos_zero]⟩
    · exact ⟨1, by norm_num [C3_cos_one]⟩
  · rintro ⟨k, rfl⟩
    fin_cases k
    · left; norm_num [C3_cos_zero]
    · right; norm_num [C3_cos_one]
    · right; norm_num [C3_cos_two]

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

