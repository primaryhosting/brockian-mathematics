/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring `/-! ... -/` before the `import`
line, so the required header appears here as an ordinary block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-! ### The primitive 20-th root of unity and the associated character -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 20)

lemma om_prim : IsPrimitiveRoot om 20 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 20 (by norm_num)

lemma om_pow20 : om ^ 20 = 1 := om_prim.pow_eq_one

lemma om_pow_congr {m n : ℕ} (h : m % 20 = n % 20) : om ^ m = om ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m 20]
  conv_rhs => rw [← Nat.div_add_mod n 20]
  rw [pow_add, pow_add, pow_mul, pow_mul, om_pow20, one_pow, one_pow, h]

lemma om_pow_eq_exp (m : ℕ) :
    om ^ m = Complex.exp ((2 * Real.pi * m / 20 : ℝ) * Complex.I) := by
  rw [om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `ωᵐ + ω⁻ᵐ = 2 cos (2πm/20)`. -/
lemma om_two_cos (m : ℕ) :
    om ^ m + om ^ (19 * m) = 2 * (Real.cos (2 * Real.pi * m / 20) : ℂ) := by
  have h1 : om ^ m * om ^ (19 * m) = 1 := by
    rw [← pow_add]
    have h : m + 19 * m = 20 * m := by ring
    rw [h, pow_mul, om_pow20, one_pow]
  have hne : om ^ m ≠ 0 := by simp [om, Complex.exp_ne_zero]
  have h2 : om ^ (19 * m) = (om ^ m)⁻¹ := by
    field_simp at h1 ⊢
    linear_combination h1
  rw [h2, om_pow_eq_exp, ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos]
  ring_nf

/-- The standard additive character of `ZMod 20` with values in `ℂ`. -/
noncomputable def e (a : ZMod 20) : ℂ := om ^ a.val

lemma e_add (a b : ZMod 20) : e (a + b) = e a * e b := by
  rw [e, e, e, ← pow_add]
  exact om_pow_congr (by rw [ZMod.val_add, Nat.mod_mod])

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_ne_zero (a : ZMod 20) : e a ≠ 0 := by
  simp [e, om, Complex.exp_ne_zero]

lemma e_pow20 (a : ZMod 20) : e a ^ 20 = 1 := by
  rw [e, ← pow_mul, mul_comm, pow_mul, om_pow20, one_pow]

lemma e_mul_pow (a k : ZMod 20) : e (a * k) = e a ^ k.val := by
  rw [e, e, ← pow_mul]
  exact om_pow_congr (by rw [ZMod.val_mul, Nat.mod_mod])

lemma e_ne_one {a : ZMod 20} (ha : a ≠ 0) : e a ≠ 1 := by
  intro h
  have hdvd : (20 : ℕ) ∣ a.val := om_prim.dvd_of_pow_eq_one a.val h
  have h1 : a.val < 20 := ZMod.val_lt a
  have h2 : a.val ≠ 0 := fun hh => ha ((ZMod.val_eq_zero a).mp hh)
  omega

/-- Orthogonality of characters on `ZMod 20`. -/
lemma sum_e (a : ZMod 20) : ∑ k : ZMod 20, e (a * k) = if a = 0 then 20 else 0 := by
  have hsum : ∑ k : ZMod 20, e (a * k) = ∑ j ∈ Finset.range 20, (e a) ^ j := by
    simp only [e_mul_pow]
    exact Complex.ext rfl rfl
  rw [hsum]
  by_cases ha : a = 0
  · simp [ha, e_zero]
  · rw [if_neg ha, geom_sum_eq (e_ne_one ha), e_pow20]
    simp

lemma e_neg (k : ZMod 20) : e (-k) = om ^ (19 * k.val) := by
  have h20 : (20 : ZMod 20) = 0 := by decide
  have hk : (-k) = 19 * k := by linear_combination (-k) * h20
  rw [hk, e, ZMod.val_mul, show ((19 : ZMod 20)).val = 19 from rfl]
  exact om_pow_congr (by rw [Nat.mod_mod])

/-! ### The cycle graph `C₂₀` and its adjacency matrix -/

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
`i` and `j` are adjacent iff they differ by `1`. -/
def adjC20 : Matrix (ZMod 20) (ZMod 20) ℂ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- `adjC20` is indeed the adjacency matrix of Mathlib's cycle graph on 20 vertices
(`ZMod 20` and `Fin 20` are the same type). -/
lemma adjC20_eq_cycleGraph : adjC20 = (SimpleGraph.cycleGraph 20).adjMatrix ℂ := by
  ext i j
  simp only [adjC20, Matrix.of_apply, SimpleGraph.adjMatrix_apply]
  congr 1
  simp [SimpleGraph.cycleGraph_adj]

/-- The DFT matrix. -/
noncomputable def dftMat : Matrix (ZMod 20) (ZMod 20) ℂ := Matrix.of fun j k => e (j * k)

/-- The inverse DFT matrix. -/
noncomputable def dftMatInv : Matrix (ZMod 20) (ZMod 20) ℂ :=
  Matrix.of fun k j => (20 : ℂ)⁻¹ * e (-(k * j))

/-- The diagonal matrix of Hückel eigenvalues `2 cos (2πk/20)`. -/
noncomputable def diagC20 : Matrix (ZMod 20) (ZMod 20) ℂ :=
  Matrix.diagonal fun k => (2 * Real.cos (2 * Real.pi * k.val / 20) : ℂ)

lemma adj_row_sum (f : ZMod 20 → ℂ) (i : ZMod 20) :
    ∑ j, adjC20 i j * f j = f (i - 1) + f (i + 1) := by
  have hne : (i - 1 : ZMod 20) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 20) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have key : ∀ j, adjC20 i j * f j
      = (if j = i - 1 then f j else 0) + (if j = i + 1 then f j else 0) := by
    intro j
    have h1 : (i - j = 1) ↔ j = i - 1 := by
      constructor <;> intro h <;> linear_combination -h
    have h2 : (j - i = 1) ↔ j = i + 1 := by
      constructor <;> intro h <;> linear_combination h
    simp only [adjC20, Matrix.of_apply, h1, h2]
    by_cases hA : j = i - 1 <;> by_cases hB : j = i + 1 <;>
      simp_all
  simp only [key, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ (i - 1) f, Finset.sum_ite_eq' Finset.univ (i + 1) f]
  simp

lemma adj_mul_dft : adjC20 * dftMat = dftMat * diagC20 := by
  ext i k
  rw [Matrix.mul_apply, adj_row_sum (fun j => dftMat j k) i]
  simp only [dftMat, Matrix.of_apply, diagC20, Matrix.mul_diagonal]
  have h1 : (i - 1) * k = i * k + (-k) := by ring
  have h2 : (i + 1) * k = i * k + k := by ring
  rw [h1, h2, e_add, e_add, ← mul_add, e_neg, show e k = om ^ k.val from rfl,
    add_comm (om ^ (19 * k.val)) (om ^ k.val), om_two_cos]

lemma dft_mul_inv : dftMat * dftMatInv = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [dftMat, dftMatInv, Matrix.of_apply]
  have hkey : ∀ k : ZMod 20, e (i * k) * ((20 : ℂ)⁻¹ * e (-(k * j)))
      = (20 : ℂ)⁻¹ * e ((i - j) * k) := by
    intro k
    have h : (i - j) * k = i * k + -(k * j) := by ring
    rw [h, e_add]
    ring
  simp only [hkey, ← Finset.mul_sum, sum_e (i - j)]
  by_cases hij : i = j
  · simp [hij, Matrix.one_apply]
  · have : i - j ≠ 0 := sub_ne_zero_of_ne hij
    simp [this, hij]

lemma isUnit_dftMat : IsUnit dftMat :=
  ⟨⟨dftMat, dftMatInv, dft_mul_inv, mul_eq_one_comm.mp dft_mul_inv⟩, rfl⟩

lemma spectrum_diagonal (d : ZMod 20 → ℂ) :
    spectrum ℂ (Matrix.diagonal d) = Set.range d := by
  ext l
  rw [spectrum.mem_iff]
  have halg : (algebraMap ℂ (Matrix (ZMod 20) (ZMod 20) ℂ)) l - Matrix.diagonal d
      = Matrix.diagonal (fun k => l - d k) := by
    rw [Matrix.algebraMap_eq_diagonal, ← Matrix.diagonal_sub]
    rfl
  rw [halg, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero,
    not_not, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, (sub_eq_zero.mp hk).symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ k, by rw [hk, sub_self]⟩

/-- **Hückel theory for C₂₀.** The adjacency eigenvalues of the cycle graph `C₂₀`
(equivalently, up to the affine transformation `α + βx`, the Hückel MO energies of the
20-membered carbon ring) are exactly `2 cos (2πk/20)` for `k = 0, …, 19`. -/
theorem huckel_C20 :
    spectrum ℂ ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) =
      {z : ℂ | ∃ k : ℕ, k < 20 ∧ z = (2 * Real.cos (2 * Real.pi * k / 20) : ℝ)} := by
  rw [← adjC20_eq_cycleGraph]
  obtain ⟨u, hu⟩ := isUnit_dftMat
  have hconj : adjC20 = (u : Matrix (ZMod 20) (ZMod 20) ℂ) * diagC20
      * ((u⁻¹ : (Matrix (ZMod 20) (ZMod 20) ℂ)ˣ) : Matrix (ZMod 20) (ZMod 20) ℂ) := by
    have h : adjC20 * (u : Matrix (ZMod 20) (ZMod 20) ℂ)
        = (u : Matrix (ZMod 20) (ZMod 20) ℂ) * diagC20 := by
      rw [hu]; exact adj_mul_dft
    rw [← h, mul_assoc, u.mul_inv, mul_one]
  rw [hconj, spectrum.units_conjugate, diagC20, spectrum_diagonal]
  ext z
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, ZMod.val_lt k, by push_cast; ring⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(k : ZMod 20), ?_⟩
    rw [ZMod.val_natCast_of_lt hk]
    push_cast
    ring

/-- The explicit Hückel eigenvectors of `C₂₀`: the `k`-th Fourier mode
`j ↦ exp (2πi jk/20)` is an eigenvector of the adjacency matrix with eigenvalue
`2 cos (2πk/20)`. -/
theorem huckel_C20_eigenvector (k : ZMod 20) :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) *ᵥ (fun j : ZMod 20 => e (j * k))
      = (2 * Real.cos (2 * Real.pi * k.val / 20) : ℂ) • (fun j : ZMod 20 => e (j * k)) := by
  rw [← adjC20_eq_cycleGraph]
  funext i
  have h := congrFun (congrFun adj_mul_dft i) k
  rw [diagC20, Matrix.mul_diagonal, Matrix.mul_apply] at h
  simp only [dftMat, Matrix.of_apply] at h
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

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

