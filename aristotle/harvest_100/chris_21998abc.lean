import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open scoped Matrix

/-! ### A primitive 14-th root of unity and the associated character -/

/-- A primitive 14-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 14)

theorem om_ne_zero : om ≠ 0 := Complex.exp_ne_zero _

theorem om_isPrimitiveRoot : IsPrimitiveRoot om 14 := by
  have h := Complex.isPrimitiveRoot_exp 14 (by norm_num)
  norm_num at h
  simpa [om] using h

theorem om_pow_14 : om ^ (14 : ℕ) = 1 := om_isPrimitiveRoot.pow_eq_one

theorem om_zpow_14 : om ^ (14 : ℤ) = 1 := by
  rw [show ((14 : ℤ)) = ((14 : ℕ) : ℤ) by norm_num, zpow_natCast, om_pow_14]

/-- `ee m = ω ^ m`, a character of `ℤ` with period `14`. -/
noncomputable def ee (m : ℤ) : ℂ := om ^ m

theorem ee_ne_zero (m : ℤ) : ee m ≠ 0 := zpow_ne_zero _ om_ne_zero

theorem ee_add (a b : ℤ) : ee (a + b) = ee a * ee b := zpow_add₀ om_ne_zero a b

theorem ee_zero : ee 0 = 1 := by simp [ee]

theorem ee_congr {a b : ℤ} (h : a ≡ b [ZMOD 14]) : ee a = ee b := by
  obtain ⟨t, ht⟩ : (14 : ℤ) ∣ b - a := Int.ModEq.dvd h
  have hb : b = a + 14 * t := by omega
  rw [hb]
  simp only [ee]
  rw [zpow_add₀ om_ne_zero, zpow_mul, om_zpow_14, one_zpow, mul_one]

theorem ee_eq_one_iff {d : ℤ} : ee d = 1 ↔ (14 : ℤ) ∣ d :=
  om_isPrimitiveRoot.zpow_eq_one_iff_dvd d

theorem ee_intCast_mul (a d : ℤ) : ee (a * d) = ee d ^ a := by
  rw [ee, ee, mul_comm, zpow_mul]

/-! ### Congruences for `Fin 14` arithmetic -/

theorem fin_val_add_cong (j k : Fin 14) :
    (((j + k : Fin 14) : ℕ) : ℤ) ≡ ((j : ℕ) : ℤ) + ((k : ℕ) : ℤ) [ZMOD 14] := by
  have hj := j.isLt
  have hk := k.isLt
  simp only [Fin.val_add, Int.ModEq]
  omega

/-! ### The eigenvalues -/

/-- The `k`-th Hückel eigenvalue of `C₁₄`. -/
noncomputable def lam (k : Fin 14) : ℝ := 2 * Real.cos (2 * Real.pi * (k : ℕ) / 14)

theorem ee_eq_exp (m : ℤ) :
    ee m = Complex.exp ((2 * Real.pi * m / 14 : ℝ) * Complex.I) := by
  rw [ee, om, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem ee_add_ee_neg (k : Fin 14) :
    ee ((k : ℕ) : ℤ) + ee (-((k : ℕ) : ℤ)) = (lam k : ℂ) := by
  set θ : ℝ := 2 * Real.pi * ((k : ℕ) : ℝ) / 14 with hdef
  have h1 : ee ((k : ℕ) : ℤ) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [ee_eq_exp]
    norm_num [hdef]
  have h2 : ee (-((k : ℕ) : ℤ)) = Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [ee_eq_exp]
    congr 1
    push_cast [hdef]
    ring
  rw [h1, h2, lam, ← hdef, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos,
    Complex.cos, ← neg_mul]
  ring

/-! ### Diagonalisation -/

/-- The (unnormalised) discrete Fourier transform matrix. -/
noncomputable def Fm : Matrix (Fin 14) (Fin 14) ℂ :=
  fun j k => ee (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ))

/-- The inverse of `Fm`. -/
noncomputable def Gm : Matrix (Fin 14) (Fin 14) ℂ :=
  fun k l => (14 : ℂ)⁻¹ * ee (-(((k : ℕ) : ℤ) * ((l : ℕ) : ℤ)))

/-- The diagonal matrix of Hückel eigenvalues. -/
noncomputable def Dm : Matrix (Fin 14) (Fin 14) ℂ := Matrix.diagonal (fun k => (lam k : ℂ))

theorem sum_ee (d : ℤ) (hd : ¬ (14 : ℤ) ∣ d) :
    ∑ k : Fin 14, ee (((k : ℕ) : ℤ) * d) = 0 := by
  have hz : ee d ≠ 1 := fun h => hd (ee_eq_one_iff.mp h)
  have hterm : ∀ k : Fin 14, ee (((k : ℕ) : ℤ) * d) = (ee d) ^ ((k : ℕ)) := by
    intro k
    rw [ee_intCast_mul, zpow_natCast]
  simp only [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun i => (ee d) ^ i) 14, geom_sum_eq hz]
  have h14 : (ee d) ^ (14 : ℕ) = 1 := by
    rw [ee, ← zpow_natCast (om ^ d) 14, ← zpow_mul, mul_comm, zpow_mul,
      show ((14 : ℕ) : ℤ) = (14 : ℤ) from by norm_num, om_zpow_14, one_zpow]
  rw [h14, sub_self, zero_div]

theorem sum_ee_zero : ∑ _k : Fin 14, ee (0 : ℤ) = (14 : ℂ) := by
  simp [ee]

theorem Fm_mul_Gm : Fm * Gm = 1 := by
  ext j l
  simp only [Matrix.mul_apply, Fm, Gm]
  have hterm : ∀ k : Fin 14,
      ee (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ)) *
          ((14 : ℂ)⁻¹ * ee (-(((k : ℕ) : ℤ) * ((l : ℕ) : ℤ)))) =
        (14 : ℂ)⁻¹ * ee (((k : ℕ) : ℤ) * (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ))) := by
    intro k
    rw [show ((k : ℕ) : ℤ) * (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ))
        = ((j : ℕ) : ℤ) * ((k : ℕ) : ℤ) + -(((k : ℕ) : ℤ) * ((l : ℕ) : ℤ)) by ring, ee_add]
    ring
  simp only [hterm, ← Finset.mul_sum]
  by_cases h : j = l
  · subst h
    rw [show ((j : ℕ) : ℤ) - ((j : ℕ) : ℤ) = 0 by ring]
    simp only [mul_zero]
    rw [sum_ee_zero, Matrix.one_apply_eq]
    norm_num
  · have hd : ¬ (14 : ℤ) ∣ (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)) := by
      have hj := j.isLt
      have hl := l.isLt
      have hne : ((j : ℕ) : ℤ) ≠ ((l : ℕ) : ℤ) := by
        simpa [Fin.ext_iff] using h
      omega
    rw [sum_ee _ hd, mul_zero, Matrix.one_apply_ne h]

theorem Gm_mul_Fm : Gm * Fm = 1 := mul_eq_one_comm.mp Fm_mul_Gm

theorem Fm_succ (j l : Fin 14) : Fm (j + 1) l = Fm j l * ee ((l : ℕ) : ℤ) := by
  have hc := fin_val_add_cong j 1
  have h1 : (((1 : Fin 14) : ℕ) : ℤ) = 1 := by norm_num
  rw [h1] at hc
  have : (((j + 1 : Fin 14) : ℕ) : ℤ) * ((l : ℕ) : ℤ)
      ≡ (((j : ℕ) : ℤ) + 1) * ((l : ℕ) : ℤ) [ZMOD 14] := Int.ModEq.mul_right _ hc
  rw [Fm, ee_congr this,
    show (((j : ℕ) : ℤ) + 1) * ((l : ℕ) : ℤ)
      = ((j : ℕ) : ℤ) * ((l : ℕ) : ℤ) + ((l : ℕ) : ℤ) by ring, ee_add]
  rfl

theorem Fm_pred (j l : Fin 14) : Fm (j - 1) l = Fm j l * ee (-((l : ℕ) : ℤ)) := by
  have hc := fin_val_add_cong (j - 1) 1
  have h1 : (((1 : Fin 14) : ℕ) : ℤ) = 1 := by norm_num
  rw [h1, show (j - 1 : Fin 14) + 1 = j from sub_add_cancel j 1] at hc
  have hc' : (((j - 1 : Fin 14) : ℕ) : ℤ) ≡ ((j : ℕ) : ℤ) - 1 [ZMOD 14] := by
    have := Int.ModEq.sub_right 1 hc.symm
    simpa using this
  have : (((j - 1 : Fin 14) : ℕ) : ℤ) * ((l : ℕ) : ℤ)
      ≡ (((j : ℕ) : ℤ) - 1) * ((l : ℕ) : ℤ) [ZMOD 14] := Int.ModEq.mul_right _ hc'
  rw [Fm, ee_congr this,
    show (((j : ℕ) : ℤ) - 1) * ((l : ℕ) : ℤ)
      = ((j : ℕ) : ℤ) * ((l : ℕ) : ℤ) + -((l : ℕ) : ℤ) by ring, ee_add]
  rfl

theorem adj_mul_Fm :
    (SimpleGraph.cycleGraph 14).adjMatrix ℂ * Fm = Fm * Dm := by
  ext j l
  rw [SimpleGraph.adjMatrix_mul_apply, SimpleGraph.cycleGraph_neighborFinset (n := 12)]
  have hne : (j - 1 : Fin 14) ≠ j + 1 := by
    intro h
    have h2 : j = j + (1 + 1) := by
      rw [← add_assoc]
      exact sub_eq_iff_eq_add.mp h
    have h3 : (0 : Fin 14) = 1 + 1 := by
      nth_rewrite 1 [show j = j + 0 from (add_zero j).symm] at h2
      exact add_left_cancel h2
    exact absurd h3 (by decide)
  rw [Finset.sum_pair hne, Fm_succ, Fm_pred]
  have hD : (Fm * Dm) j l = Fm j l * (lam l : ℂ) := by
    simp [Matrix.mul_apply, Dm, Matrix.diagonal_apply, Finset.sum_ite_eq']
  rw [hD, ← ee_add_ee_neg l]
  ring

theorem adj_eq_conj :
    (SimpleGraph.cycleGraph 14).adjMatrix ℂ = Fm * Dm * Gm := by
  calc (SimpleGraph.cycleGraph 14).adjMatrix ℂ
      = (SimpleGraph.cycleGraph 14).adjMatrix ℂ * (Fm * Gm) := by rw [Fm_mul_Gm, Matrix.mul_one]
    _ = ((SimpleGraph.cycleGraph 14).adjMatrix ℂ * Fm) * Gm := by rw [Matrix.mul_assoc]
    _ = Fm * Dm * Gm := by rw [adj_mul_Fm]

/-- **Hückel theory for `C₁₄`**: the eigenvalues (the spectrum) of the adjacency matrix of the
cycle graph `C₁₄` are exactly the numbers `2 cos (2πk/14)`, `k = 0, …, 13`. -/
theorem huckel_C14 :
    spectrum ℂ ((SimpleGraph.cycleGraph 14).adjMatrix ℂ) =
      Set.range (fun k : Fin 14 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 14) : ℝ) : ℂ)) := by
  let u : (Matrix (Fin 14) (Fin 14) ℂ)ˣ := ⟨Fm, Gm, Fm_mul_Gm, Gm_mul_Fm⟩
  have hconj : (SimpleGraph.cycleGraph 14).adjMatrix ℂ
      = (u : Matrix (Fin 14) (Fin 14) ℂ) * Dm * (↑u⁻¹ : Matrix (Fin 14) (Fin 14) ℂ) :=
    adj_eq_conj
  rw [hconj, spectrum.units_conjugate, Dm, spectrum_diagonal]
  rfl

/-- The explicit Hückel eigenvectors of `C₁₄`: the `k`-th column of the discrete Fourier
transform matrix is a nonzero eigenvector of the adjacency matrix for the eigenvalue
`2 cos (2πk/14)`. -/
theorem huckel_C14_eigenvector (k : Fin 14) :
    (fun j : Fin 14 => Fm j k) ≠ 0 ∧
      (SimpleGraph.cycleGraph 14).adjMatrix ℂ *ᵥ (fun j : Fin 14 => Fm j k) =
        ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 14) : ℝ) : ℂ) • (fun j : Fin 14 => Fm j k) := by
  constructor
  · intro h
    have h0 : Fm 0 k = 0 := congrFun h 0
    rw [Fm] at h0
    exact ee_ne_zero _ h0
  · funext j
    have h := congrFun (congrFun adj_mul_Fm j) k
    simp only [Matrix.mul_apply] at h
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [h]
    simp only [Dm, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [lam]
    ring

end Chem

