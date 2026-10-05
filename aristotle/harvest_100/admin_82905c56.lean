/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of a
16-membered annulene, with `α = 0`, `β = 1`). -/
noncomputable def C16 : Matrix (Fin 16) (Fin 16) ℂ :=
  (SimpleGraph.cycleGraph 16).adjMatrix ℂ

/-- The `k`-th Hückel energy level of `C₁₆`: `2 cos (2πk/16)`. -/
noncomputable def huckelLevel (k : Fin 16) : ℂ :=
  2 * Real.cos (2 * Real.pi * (k : ℕ) / 16)

/-- A primitive 16-th root of unity. -/
noncomputable def zeta16 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The Fourier (Vandermonde) matrix diagonalizing `C16`. -/
noncomputable def dft16 : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.vandermonde (fun j : Fin 16 => zeta16 ^ (j : ℕ))

lemma isPrimitiveRoot_zeta16 : IsPrimitiveRoot zeta16 16 := by
  have := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  simpa [zeta16] using this

lemma zeta16_pow_sixteen : zeta16 ^ 16 = 1 := isPrimitiveRoot_zeta16.pow_eq_one

lemma zeta16_pow_mod (a : ℕ) : zeta16 ^ a = zeta16 ^ (a % 16) := by
  conv_lhs => rw [← Nat.div_add_mod a 16]
  rw [pow_add, pow_mul, zeta16_pow_sixteen, one_pow, one_mul]

lemma zeta16_pow_congr {a b : ℕ} (h : a % 16 = b % 16) : zeta16 ^ a = zeta16 ^ b := by
  rw [zeta16_pow_mod a, zeta16_pow_mod b, h]

lemma zeta16_pow_eq_exp (m : ℕ) :
    zeta16 ^ m = Complex.exp (((2 * Real.pi * m / 16 : ℝ) : ℂ) * Complex.I) := by
  rw [zeta16, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `ζ^m + ζ^{-m} = 2 cos (2πm/16)`. -/
lemma zeta16_pow_add_inv (m : ℕ) :
    zeta16 ^ m + (zeta16 ^ m)⁻¹ = 2 * Real.cos (2 * Real.pi * m / 16) := by
  rw [zeta16_pow_eq_exp, ← Complex.exp_neg,
    show -(((2 * Real.pi * m / 16 : ℝ) : ℂ) * Complex.I)
        = ((-(2 * Real.pi * m / 16) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

lemma C16_apply (j l : Fin 16) : C16 j l = if l = j - 1 ∨ l = j + 1 then 1 else 0 := by
  have hadj : ∀ j l : Fin 16,
      (SimpleGraph.cycleGraph 16).Adj j l ↔ (l = j - 1 ∨ l = j + 1) := by decide
  rw [C16, SimpleGraph.adjMatrix_apply]
  simp only [hadj]

/-- Multiplying by the adjacency matrix of `C₁₆` sums the two neighbouring values. -/
lemma C16_row_sum (f : Fin 16 → ℂ) (j : Fin 16) :
    ∑ l, C16 j l * f l = f (j - 1) + f (j + 1) := by
  have hfilter : ∀ j : Fin 16,
      Finset.univ.filter (fun l : Fin 16 => l = j - 1 ∨ l = j + 1) = {j - 1, j + 1} := by decide
  have hne : ∀ j : Fin 16, j - 1 ≠ j + 1 := by decide
  have : ∑ l, C16 j l * f l = ∑ l ∈ Finset.univ.filter
      (fun l : Fin 16 => l = j - 1 ∨ l = j + 1), f l := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [C16_apply]
    split <;> simp
  rw [this, hfilter j, Finset.sum_pair (hne j)]

/-- The key diagonalization identity `A · U = U · D`. -/
lemma C16_mul_dft16 : C16 * dft16 = dft16 * Matrix.diagonal huckelLevel := by
  ext j k
  have hsucc : ∀ j : Fin 16, ((j + 1 : Fin 16) : ℕ) % 16 = ((j : ℕ) + 1) % 16 := by decide
  have hpred : ∀ j : Fin 16, ((j - 1 : Fin 16) : ℕ) % 16 = ((j : ℕ) + 15) % 16 := by decide
  have hentry : ∀ l : Fin 16, dft16 l k = zeta16 ^ ((l : ℕ) * (k : ℕ)) := by
    intro l
    rw [dft16, Matrix.vandermonde_apply, ← pow_mul]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [show ∑ l, C16 j l * dft16 l k = dft16 (j - 1) k + dft16 (j + 1) k from
    C16_row_sum (fun l => dft16 l k) j]
  rw [hentry, hentry]
  have h1 : zeta16 ^ (((j + 1 : Fin 16) : ℕ) * (k : ℕ))
      = zeta16 ^ ((j : ℕ) * (k : ℕ)) * zeta16 ^ (k : ℕ) := by
    rw [← pow_add]
    refine zeta16_pow_congr ?_
    calc ((j + 1 : Fin 16) : ℕ) * (k : ℕ) % 16
        = (((j : ℕ) + 1) * (k : ℕ)) % 16 := by
          rw [Nat.mul_mod, hsucc j, ← Nat.mul_mod]
      _ = ((j : ℕ) * (k : ℕ) + (k : ℕ)) % 16 := by ring_nf
  have h2 : zeta16 ^ (((j - 1 : Fin 16) : ℕ) * (k : ℕ))
      = zeta16 ^ ((j : ℕ) * (k : ℕ)) * (zeta16 ^ (k : ℕ))⁻¹ := by
    have hinv : (zeta16 ^ (k : ℕ))⁻¹ = zeta16 ^ (15 * (k : ℕ)) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, show (k : ℕ) + 15 * (k : ℕ) = 16 * (k : ℕ) by ring, pow_mul,
        zeta16_pow_sixteen, one_pow]
    rw [hinv, ← pow_add]
    refine zeta16_pow_congr ?_
    calc ((j - 1 : Fin 16) : ℕ) * (k : ℕ) % 16
        = (((j : ℕ) + 15) * (k : ℕ)) % 16 := by
          rw [Nat.mul_mod, hpred j, ← Nat.mul_mod]
      _ = ((j : ℕ) * (k : ℕ) + 15 * (k : ℕ)) % 16 := by ring_nf
  rw [h1, h2]
  rw [Finset.sum_eq_single k (fun b _ hb => by
      rw [Matrix.diagonal_apply_ne _ hb, mul_zero]) (by simp)]
  rw [hentry, Matrix.diagonal_apply_eq, huckelLevel, ← zeta16_pow_add_inv (k : ℕ)]
  ring

lemma dft16_isUnit : IsUnit dft16 := by
  rw [Matrix.isUnit_iff_isUnit_det]
  refine isUnit_iff_ne_zero.mpr ?_
  rw [dft16, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => ?_))
  have hij : i < j := Finset.mem_Ioi.mp hj
  have hij' : (i : ℕ) < (j : ℕ) := hij
  refine sub_ne_zero.mpr (fun h => ?_)
  have := isPrimitiveRoot_zeta16.pow_inj j.isLt i.isLt h
  omega

theorem C16_eq_conj :
    C16 = dft16 * Matrix.diagonal huckelLevel * dft16⁻¹ := by
  rw [← C16_mul_dft16, Matrix.mul_nonsing_inv_cancel_right]
  exact (Matrix.isUnit_iff_isUnit_det _).mp dft16_isUnit

theorem C16_charpoly :
    C16.charpoly = ∏ k : Fin 16, (X - C (huckelLevel k)) := by
  rw [C16_eq_conj]
  have := Matrix.charpoly_units_conj dft16_isUnit.unit (Matrix.diagonal huckelLevel)
  rw [Matrix.coe_units_inv, IsUnit.unit_spec] at this
  rw [this, Matrix.charpoly_diagonal]

lemma scalar_mulVec (mu : ℂ) (v : Fin 16 → ℂ) : (Matrix.scalar (Fin 16) mu) *ᵥ v = mu • v := by
  rw [Matrix.scalar_apply]
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

theorem C16_eigenvalue_iff (mu : ℂ) :
    (∃ v : Fin 16 → ℂ, v ≠ 0 ∧ C16 *ᵥ v = mu • v) ↔ ∃ k : Fin 16, mu = huckelLevel k := by
  have hkey : (∃ v : Fin 16 → ℂ, v ≠ 0 ∧ (Matrix.scalar (Fin 16) mu - C16) *ᵥ v = 0) ↔
      (Matrix.scalar (Fin 16) mu - C16).det = 0 := Matrix.exists_mulVec_eq_zero_iff
  have hdet : (Matrix.scalar (Fin 16) mu - C16).det = ∏ k : Fin 16, (mu - huckelLevel k) := by
    rw [← Matrix.eval_charpoly, C16_charpoly]
    simp [Polynomial.eval_prod]
  constructor
  · rintro ⟨v, hv, hAv⟩
    have h0 : (Matrix.scalar (Fin 16) mu - C16) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, hAv, scalar_mulVec, sub_self]
    have := hkey.mp ⟨v, hv, h0⟩
    rw [hdet] at this
    obtain ⟨k, _, hk⟩ := Finset.prod_eq_zero_iff.mp this
    exact ⟨k, by linear_combination hk⟩
  · rintro ⟨k, rfl⟩
    have : (Matrix.scalar (Fin 16) (huckelLevel k) - C16).det = 0 := by
      rw [hdet]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by ring)
    obtain ⟨v, hv, h0⟩ := hkey.mpr this
    refine ⟨v, hv, ?_⟩
    have h1 : (Matrix.scalar (Fin 16) (huckelLevel k)) *ᵥ v - C16 *ᵥ v = 0 := by
      rw [← Matrix.sub_mulVec]; exact h0
    have h2 := sub_eq_zero.mp h1
    rw [← h2, scalar_mulVec]

/-- **Hückel theory for C₁₆.**  The adjacency (Hückel) matrix of the cycle graph `C₁₆`
has characteristic polynomial `∏_{k=0}^{15} (X - 2 cos (2πk/16))`; equivalently its
eigenvalues are exactly the numbers `2 cos (2πk/16)` for `k = 0, …, 15`. -/
theorem huckel_C16 :
    ((SimpleGraph.cycleGraph 16).adjMatrix ℂ).charpoly
        = ∏ k : Fin 16, (X - C (2 * (Real.cos (2 * Real.pi * (k : ℕ) / 16) : ℂ)))
      ∧ ∀ mu : ℂ,
        (∃ v : Fin 16 → ℂ, v ≠ 0 ∧ ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) *ᵥ v = mu • v) ↔
          ∃ k : Fin 16, mu = 2 * (Real.cos (2 * Real.pi * (k : ℕ) / 16) : ℂ) := by
  exact ⟨C16_charpoly, C16_eigenvalue_iff⟩

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

