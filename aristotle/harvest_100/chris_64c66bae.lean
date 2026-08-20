/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex (I)
open Matrix

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * I / 19)

/-- The character `Fin 19 → ℂ`, `a ↦ ω ^ a`. -/
noncomputable def ee (a : Fin 19) : ℂ := om ^ (a : ℕ)

/-- The Hückel eigenvalues of the cycle `C₁₉`. -/
noncomputable def mu (k : Fin 19) : ℂ := 2 * Real.cos (2 * Real.pi * (k : ℕ) / 19)

/-- The adjacency matrix of the cycle graph `C₁₉` over `ℂ`. -/
noncomputable def AC19 : Matrix (Fin 19) (Fin 19) ℂ :=
  (SimpleGraph.cycleGraph 19).adjMatrix ℂ

/-- The (unnormalized) discrete Fourier matrix. -/
noncomputable def Fmat : Matrix (Fin 19) (Fin 19) ℂ := Matrix.of fun i k => ee (i * k)

theorem om_prim : IsPrimitiveRoot om 19 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 19 (by norm_num)

theorem om_pow_19 : om ^ (19 : ℕ) = 1 := om_prim.pow_eq_one

theorem om_pow_mod (m : ℕ) : om ^ (m % 19) = om ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 19]
  rw [pow_add, pow_mul, om_pow_19, one_pow, one_mul]

theorem ee_add (a b : Fin 19) : ee (a + b) = ee a * ee b := by
  simp only [ee, Fin.val_add, om_pow_mod, pow_add]

theorem ee_zero : ee 0 = 1 := by simp [ee]

theorem ee_ne_one {d : Fin 19} (hd : d ≠ 0) : ee d ≠ 1 := by
  intro h
  have hdvd : (19 : ℕ) ∣ (d : ℕ) := (om_prim.pow_eq_one_iff_dvd _).mp h
  have hlt : (d : ℕ) < 19 := d.isLt
  have hpos : (d : ℕ) ≠ 0 := fun h0 => hd (Fin.val_eq_zero_iff.mp h0)
  omega

theorem ee_mul (k d : Fin 19) : ee (k * d) = ee d ^ (k : ℕ) := by
  simp only [ee, Fin.val_mul, om_pow_mod, pow_mul]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem ee_pow_19 (d : Fin 19) : ee d ^ (19 : ℕ) = 1 := by
  rw [ee, ← pow_mul, Nat.mul_comm, pow_mul, om_pow_19, one_pow]

theorem sum_ee (d : Fin 19) : ∑ k : Fin 19, ee (k * d) = if d = 0 then 19 else 0 := by
  simp only [ee_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => ee d ^ i) 19]
  by_cases hd : d = 0
  · subst hd
    simp [ee_zero]
  · rw [if_neg hd, geom_sum_eq (ee_ne_one hd), ee_pow_19, sub_self, zero_div]

theorem ee_eq_exp (k : Fin 19) :
    ee k = Complex.exp ((2 * Real.pi * (k : ℕ) / 19 : ℝ) * I) := by
  rw [ee, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem ee_add_neg (k : Fin 19) : ee k + ee (-k) = mu k := by
  have h1 : ee k * ee (-k) = 1 := by
    rw [← ee_add, add_neg_cancel, ee_zero]
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 19 with ht
  have hk : ee k = Complex.exp ((t : ℝ) * I) := ee_eq_exp k
  have hnk : ee (-k) = Complex.exp (-((t : ℝ) * I)) := by
    have hne : Complex.exp ((t : ℝ) * I) ≠ 0 := Complex.exp_ne_zero _
    have := h1
    rw [hk] at this
    rw [Complex.exp_neg]
    field_simp
    linear_combination this
  rw [hk, hnk, mu, ← ht, Complex.ofReal_cos, Complex.cos]
  ring_nf

theorem sub_one_ne_add_one : ∀ i : Fin 19, i - 1 ≠ i + 1 := by decide

theorem adjMatrix_mulVec_ee (k : Fin 19) :
    AC19 *ᵥ (fun i => ee (i * k)) = mu k • (fun i => ee (i * k)) := by
  funext i
  have hnbr : (SimpleGraph.cycleGraph 19).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 17)
  have e1 : ee ((i + 1) * k) = ee (i * k) * ee k := by
    rw [← ee_add, add_mul, one_mul]
  have e2 : ee ((i - 1) * k) = ee (i * k) * ee (-k) := by
    rw [← ee_add, sub_mul, one_mul, sub_eq_add_neg]
  rw [AC19, SimpleGraph.adjMatrix_mulVec_apply, hnbr,
    Finset.sum_pair (sub_one_ne_add_one i), e1, e2, Pi.smul_apply, smul_eq_mul, ← ee_add_neg]
  ring

/-- The inverse (up to normalization) of the Fourier matrix. -/
noncomputable def Gmat : Matrix (Fin 19) (Fin 19) ℂ :=
  Matrix.of fun k j => (19 : ℂ)⁻¹ * ee (-(k * j))

theorem Fmat_mul_Gmat : Fmat * Gmat = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 19, Fmat i k * Gmat k j = (19 : ℂ)⁻¹ * ee (k * (i - j)) := by
    intro k
    simp only [Fmat, Gmat, Matrix.of_apply]
    rw [show ee (i * k) * ((19 : ℂ)⁻¹ * ee (-(k * j)))
        = (19 : ℂ)⁻¹ * (ee (i * k) * ee (-(k * j))) by ring, ← ee_add]
    congr 2
    rw [mul_comm i k, ← mul_neg, ← mul_add, ← sub_eq_add_neg]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, sum_ee]
  by_cases h : i = j
  · subst h
    norm_num
  · rw [if_neg (sub_ne_zero_of_ne h), Matrix.one_apply_ne h, mul_zero]

theorem Fmat_unit :
    ∃ u : (Matrix (Fin 19) (Fin 19) ℂ)ˣ, (u : Matrix (Fin 19) (Fin 19) ℂ) = Fmat :=
  ⟨⟨Fmat, Gmat, Fmat_mul_Gmat, mul_eq_one_comm.mp Fmat_mul_Gmat⟩, rfl⟩

theorem AC19_mul_Fmat : AC19 * Fmat = Fmat * Matrix.diagonal mu := by
  ext i k
  have h := congrFun (adjMatrix_mulVec_ee k) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  simpa [Fmat, mul_comm] using h

/-- **Hückel theory for the cycle `C₁₉`**: the eigenvalues (spectrum) of the adjacency
matrix of the cycle graph on 19 vertices are exactly `2 cos (2πk/19)` for `k = 0, …, 18`. -/
theorem huckel_C19 :
    spectrum ℂ ((SimpleGraph.cycleGraph 19).adjMatrix ℂ) =
      {z : ℂ | ∃ k : ℕ, k < 19 ∧ z = 2 * Real.cos (2 * Real.pi * k / 19)} := by
  obtain ⟨u, hu⟩ := Fmat_unit
  have hA : AC19 = (u : Matrix (Fin 19) (Fin 19) ℂ) * Matrix.diagonal mu *
      ((u⁻¹ : (Matrix (Fin 19) (Fin 19) ℂ)ˣ) : Matrix (Fin 19) (Fin 19) ℂ) := by
    rw [hu, ← AC19_mul_Fmat, ← hu, Matrix.mul_assoc, u.mul_inv, Matrix.mul_one]
  have hspec : spectrum ℂ AC19 = spectrum ℂ (Matrix.diagonal mu) := by
    rw [hA]; exact spectrum.units_conjugate
  have hdiag : spectrum ℂ (Matrix.diagonal mu) = Set.range mu := by
    ext z
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_diagonal, Polynomial.IsRoot,
      Polynomial.eval_prod]
    rw [Finset.prod_eq_zero_iff]
    simp [sub_eq_zero, eq_comm]
  show spectrum ℂ AC19 = _
  rw [hspec, hdiag]
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨(k : ℕ), k.isLt, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

/-- The explicit Hückel molecular orbitals of `C₁₉`: for each `k`, the vector
`j ↦ exp (2πi j k / 19)` is an eigenvector of the adjacency matrix of the cycle graph on
19 vertices with eigenvalue `2 cos (2πk / 19)`. -/
theorem huckel_C19_eigenvector (k : Fin 19) :
    (SimpleGraph.cycleGraph 19).adjMatrix ℂ *ᵥ
        (fun j : Fin 19 => Complex.exp (2 * Real.pi * (j : ℕ) * (k : ℕ) / 19 * I)) =
      (2 * (Real.cos (2 * Real.pi * (k : ℕ) / 19) : ℂ)) •
        (fun j : Fin 19 => Complex.exp (2 * Real.pi * (j : ℕ) * (k : ℕ) / 19 * I)) := by
  have hval : ∀ j : Fin 19,
      ee (j * k) = Complex.exp (2 * Real.pi * (j : ℕ) * (k : ℕ) / 19 * I) := by
    intro j
    rw [ee, Fin.val_mul, om_pow_mod, om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h := adjMatrix_mulVec_ee k
  simp only [hval] at h
  simpa [AC19, mu] using h

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

