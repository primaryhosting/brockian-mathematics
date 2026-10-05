/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module docstring `/-! ... -/` before `import`, so the
-- required header appears above as an ordinary block comment with identical text.)

import Mathlib

/-!
# Huckel C 11

The adjacency eigenvalues of the cycle graph `C₁₁` are `2·cos(2πk/11)` for `k = 0, …, 10`.

The proof diagonalizes the adjacency matrix `A` of `SimpleGraph.cycleGraph 11` by the
discrete Fourier (Vandermonde) matrix `U j k = ω^{jk}`, where `ω = exp(2πi/11)`:
`A * U = U * diagonal d` with `d k = ω^k + ω^{-k} = 2 cos (2πk/11)`.
Since `det U ≠ 0` (`Matrix.det_vandermonde_ne_zero_iff`, `ω` being a primitive root),
`det (A - z) = ∏ k (d k - z)`, and `Matrix.exists_mulVec_eq_zero_iff` converts this into
the statement about eigenvalues.
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 11-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 11)

/-- The adjacency matrix of the cycle graph `C₁₁`. -/
noncomputable def AC11 : Matrix (Fin 11) (Fin 11) ℂ := (cycleGraph 11).adjMatrix ℂ

/-- The (Vandermonde / discrete Fourier) matrix diagonalizing `AC11`. -/
noncomputable def UC11 : Matrix (Fin 11) (Fin 11) ℂ :=
  Matrix.vandermonde (fun j : Fin 11 => om ^ (j : ℕ))

/-- The eigenvalues of `AC11`. -/
noncomputable def dC11 (k : Fin 11) : ℂ := om ^ (k : ℕ) + om ^ (10 * (k : ℕ))

theorem om_isPrimitiveRoot : IsPrimitiveRoot om 11 := by
  have h := Complex.isPrimitiveRoot_exp 11 (by norm_num)
  rw [om]
  norm_num at h ⊢
  exact h

theorem om_pow_eleven : om ^ 11 = 1 := om_isPrimitiveRoot.pow_eq_one

theorem om_pow_eq_exp (k : ℕ) :
    om ^ k = Complex.exp (((2 * Real.pi * k / 11 : ℝ) : ℂ) * Complex.I) := by
  rw [om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem dC11_eq (k : Fin 11) :
    dC11 k = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) := by
  have hprod : om ^ (k : ℕ) * om ^ (10 * (k : ℕ)) = 1 := by
    rw [← pow_add]
    have : (k : ℕ) + 10 * (k : ℕ) = 11 * (k : ℕ) := by ring
    rw [this, pow_mul, om_pow_eleven, one_pow]
  have hinv : om ^ (10 * (k : ℕ)) = (om ^ (k : ℕ))⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [mul_comm] at hprod; rw [mul_comm]; exact hprod)
  rw [dC11, hinv, om_pow_eq_exp, ← Complex.exp_neg, Complex.exp_mul_I, ← neg_mul,
    Complex.exp_mul_I]
  simp [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos]
  ring

theorem AC11_mul_UC11 : AC11 * UC11 = UC11 * Matrix.diagonal dC11 := by
  have hadj : ∀ j l : Fin 11, (cycleGraph 11).Adj j l ↔ (l = j + 10 ∨ l = j + 1) := by decide
  ext j k
  set z : ℂ := om ^ (k : ℕ) with hzdef
  have hz11 : z ^ 11 = 1 := by
    rw [hzdef, ← pow_mul, mul_comm, pow_mul, om_pow_eleven, one_pow]
  have hUentry : ∀ l : Fin 11, UC11 l k = z ^ (l : ℕ) := by
    intro l
    rw [UC11, Matrix.vandermonde_apply, hzdef, ← pow_mul, mul_comm, pow_mul]
  -- the right-hand side
  rw [Matrix.mul_diagonal, hUentry j, dC11, ← hzdef]
  have hz10 : om ^ (10 * (k : ℕ)) = z ^ 10 := by
    rw [hzdef, ← pow_mul, mul_comm]
  rw [hz10]
  -- the left-hand side
  rw [Matrix.mul_apply]
  have hstep : ∀ l : Fin 11, AC11 j l * UC11 l k
      = (if l = j + 10 then z ^ (l : ℕ) else 0) + (if l = j + 1 then z ^ (l : ℕ) else 0) := by
    intro l
    rw [AC11, SimpleGraph.adjMatrix_apply, hUentry l]
    by_cases h1 : l = j + 10 <;> by_cases h2 : l = j + 1 <;>
      simp [hadj j l, h1, h2] <;> simp_all
  rw [Finset.sum_congr rfl (fun l _ => hstep l), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have e10 : ((j + 10 : Fin 11) : ℕ) = ((j : ℕ) + 10) % 11 := by simp [Fin.add_def]
  have e1 : ((j + 1 : Fin 11) : ℕ) = ((j : ℕ) + 1) % 11 := by simp [Fin.add_def]
  rw [e10, e1]
  have hmod : ∀ m : ℕ, z ^ (m % 11) = z ^ m := by
    intro m
    conv_rhs => rw [← Nat.div_add_mod m 11]
    rw [pow_add, pow_mul, hz11, one_pow, one_mul]
  rw [hmod, hmod, pow_add, pow_add, pow_one]
  ring

theorem UC11_det_ne_zero : UC11.det ≠ 0 := by
  rw [UC11]
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro a b hab
  exact Fin.ext (om_isPrimitiveRoot.pow_inj a.isLt b.isLt hab)

theorem det_AC11_sub (z : ℂ) :
    (AC11 - z • (1 : Matrix (Fin 11) (Fin 11) ℂ)).det = ∏ k : Fin 11, (dC11 k - z) := by
  have key : (AC11 - z • (1 : Matrix (Fin 11) (Fin 11) ℂ)) * UC11
      = UC11 * Matrix.diagonal (fun k => dC11 k - z) := by
    have hd : Matrix.diagonal (fun k : Fin 11 => dC11 k - z)
        = Matrix.diagonal dC11 - z • (1 : Matrix (Fin 11) (Fin 11) ℂ) := by
      rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
    rw [hd, sub_mul, mul_sub, AC11_mul_UC11]
    congr 1
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  exact mul_right_cancel₀ UC11_det_ne_zero (by rw [hdet]; ring)

/-- **Hückel theory for the C₁₁ annulene ring.**
The eigenvalues of the adjacency matrix of the cycle graph `C₁₁` are exactly the
numbers `2 cos (2πk/11)` for `k = 0, …, 10`. -/
theorem huckel_C11 (z : ℂ) :
    (∃ v : Fin 11 → ℂ, v ≠ 0 ∧ (cycleGraph 11).adjMatrix ℂ *ᵥ v = z • v) ↔
      ∃ k : Fin 11, z = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) := by
  have hrewrite : ∀ v : Fin 11 → ℂ,
      ((cycleGraph 11).adjMatrix ℂ *ᵥ v = z • v) ↔
        (AC11 - z • (1 : Matrix (Fin 11) (Fin 11) ℂ)) *ᵥ v = 0 := by
    intro v
    rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec, Matrix.one_mulVec, AC11]
  constructor
  · rintro ⟨v, hv, hAv⟩
    have hdet : (AC11 - z • (1 : Matrix (Fin 11) (Fin 11) ℂ)).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, (hrewrite v).mp hAv⟩
    rw [det_AC11_sub] at hdet
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hdet
    exact ⟨k, by rw [← dC11_eq k]; exact (sub_eq_zero.mp hk).symm⟩
  · rintro ⟨k, hk⟩
    have hdet : (AC11 - z • (1 : Matrix (Fin 11) (Fin 11) ℂ)).det = 0 := by
      rw [det_AC11_sub]
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      rw [dC11_eq k, hk, sub_self]
    obtain ⟨v, hv, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    exact ⟨v, hv, (hrewrite v).mpr hvz⟩

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

