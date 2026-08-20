import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Polynomial

namespace Chem

/-- A primitive 9th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)

theorem om_primitive : IsPrimitiveRoot om 9 := by
  simpa [om, mul_comm, mul_assoc, mul_left_comm] using Complex.isPrimitiveRoot_exp 9 (by norm_num)

theorem om_pow_nine : om ^ 9 = 1 := om_primitive.pow_eq_one

theorem om_pow_mod (n : ℕ) : om ^ (n % 9) = om ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 9, pow_add, pow_mul, om_pow_nine, one_pow, one_mul]

theorem om_pow_congr {a b : ℕ} (h : a % 9 = b % 9) : om ^ a = om ^ b := by
  rw [← om_pow_mod a, ← om_pow_mod b, h]

theorem om_pow_ne_one {t : ℕ} (ht : t % 9 ≠ 0) : om ^ t ≠ 1 := by
  intro h
  have hdvd : (9 : ℕ) ∣ t := (om_primitive.pow_eq_one_iff_dvd _).1 h
  omega

theorem om_pow_pow_nine (t : ℕ) : (om ^ t) ^ 9 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, om_pow_nine, one_pow]

/-- Orthogonality relation for the 9th roots of unity. -/
theorem sum_om_pow (t : ℕ) :
    ∑ k : Fin 9, (om ^ t) ^ (k : ℕ) = if t % 9 = 0 then (9 : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (om ^ t) ^ i) 9]
  by_cases ht : t % 9 = 0
  · have h1 : om ^ t = 1 := by rw [← om_pow_mod, ht, pow_zero]
    simp [h1, ht]
  · rw [if_neg ht, geom_sum_eq (om_pow_ne_one ht), om_pow_pow_nine, sub_self, zero_div]

/-- The DFT matrix. -/
noncomputable def Vm : Matrix (Fin 9) (Fin 9) ℂ := fun j k => om ^ ((j : ℕ) * (k : ℕ))

/-- The (scaled) inverse DFT matrix. -/
noncomputable def Wm : Matrix (Fin 9) (Fin 9) ℂ :=
  fun k l => (9 : ℂ)⁻¹ * om ^ ((k : ℕ) * (9 - (l : ℕ)))

theorem Vm_mul_Wm : Vm * Wm = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 9, Vm j k * Wm k l
      = (9 : ℂ)⁻¹ * (om ^ ((j : ℕ) + (9 - (l : ℕ)))) ^ (k : ℕ) := by
    intro k
    have hpow : om ^ ((j : ℕ) * (k : ℕ)) * om ^ ((k : ℕ) * (9 - (l : ℕ)))
        = (om ^ ((j : ℕ) + (9 - (l : ℕ)))) ^ (k : ℕ) := by
      rw [← pow_add, ← pow_mul]
      congr 1
      ring
    simp only [Vm, Wm]
    rw [← hpow]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, sum_om_pow]
  have hl : (l : ℕ) < 9 := l.isLt
  have hj : (j : ℕ) < 9 := j.isLt
  by_cases hjl : j = l
  · subst hjl
    have h0 : ((j : ℕ) + (9 - (j : ℕ))) % 9 = 0 := by omega
    rw [if_pos h0]
    simp
  · have hne : (j : ℕ) ≠ (l : ℕ) := fun h => hjl (Fin.ext h)
    have h0 : ((j : ℕ) + (9 - (l : ℕ))) % 9 ≠ 0 := by omega
    rw [if_neg h0]
    simp [hjl]

theorem Wm_mul_Vm : Wm * Vm = 1 := mul_eq_one_comm.1 Vm_mul_Wm

/-- The eigenvalue attached to index `k` : `2 cos (2πk/9)`. -/
noncomputable def lam (k : Fin 9) : ℂ := ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 9) : ℝ) : ℂ)

theorem om_pow_add_inv (k : Fin 9) : om ^ (k : ℕ) + om ^ (8 * (k : ℕ)) = lam k := by
  have hz : om ^ (k : ℕ)
      = Complex.exp (((2 * Real.pi * (k : ℕ) / 9 : ℝ) : ℂ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hmul : om ^ (k : ℕ) * om ^ (8 * (k : ℕ)) = 1 := by
    rw [← pow_add, show (k : ℕ) + 8 * (k : ℕ) = 9 * (k : ℕ) from by ring, pow_mul, om_pow_nine,
      one_pow]
  have hinv : om ^ (8 * (k : ℕ)) = (om ^ (k : ℕ))⁻¹ := (inv_eq_of_mul_eq_one_right hmul).symm
  rw [hinv, hz, ← Complex.exp_neg, lam]
  have h2 := Complex.two_cos (((2 * Real.pi * (k : ℕ) / 9 : ℝ) : ℂ))
  rw [show -(((2 * Real.pi * (k : ℕ) / 9 : ℝ) : ℂ) * Complex.I)
      = -(((2 * Real.pi * (k : ℕ) / 9 : ℝ) : ℂ)) * Complex.I from by ring, ← h2,
    Complex.ofReal_mul, Complex.ofReal_cos]
  norm_num

theorem sub_one_ne_add_one (j : Fin 9) : (j + 1 : Fin 9) ≠ j - 1 := by revert j; decide

theorem adj_iff (j l : Fin 9) :
    (SimpleGraph.cycleGraph 9).Adj j l ↔ (l = j + 1 ∨ l = j - 1) := by revert j l; decide

theorem adj_sum (j : Fin 9) (f : Fin 9 → ℂ) :
    ∑ l : Fin 9, ((SimpleGraph.cycleGraph 9).adjMatrix ℂ) j l * f l = f (j + 1) + f (j - 1) := by
  have hterm : ∀ l : Fin 9, ((SimpleGraph.cycleGraph 9).adjMatrix ℂ) j l * f l
      = (if l = j + 1 then f l else 0) + (if l = j - 1 then f l else 0) := by
    intro l
    rw [SimpleGraph.adjMatrix_apply]
    by_cases h1 : l = j + 1
    · rw [if_pos ((adj_iff j l).2 (Or.inl h1)), if_pos h1,
        if_neg (by rw [h1]; exact sub_one_ne_add_one j), one_mul, add_zero]
    · by_cases h2 : l = j - 1
      · rw [if_pos ((adj_iff j l).2 (Or.inr h2)), if_pos h2, if_neg h1, one_mul, zero_add]
      · rw [if_neg (fun h => ((adj_iff j l).1 h).elim h1 h2), if_neg h1, if_neg h2, zero_mul,
          add_zero]
  rw [Finset.sum_congr rfl (fun l _ => hterm l), Finset.sum_add_distrib]
  simp

theorem adj_mul_Vm :
    (SimpleGraph.cycleGraph 9).adjMatrix ℂ * Vm = Vm * Matrix.diagonal lam := by
  ext j k
  rw [Matrix.mul_apply, adj_sum j (fun l => Vm l k), Matrix.mul_diagonal]
  have h1 : ((j + 1 : Fin 9) : ℕ) = ((j : ℕ) + 1) % 9 := by revert j; decide
  have h2 : ((j - 1 : Fin 9) : ℕ) = ((j : ℕ) + 8) % 9 := by revert j; decide
  have e1 : Vm (j + 1) k = om ^ ((j : ℕ) * (k : ℕ)) * om ^ ((k : ℕ)) := by
    simp only [Vm, h1, ← pow_add]
    refine om_pow_congr ?_
    have h := Nat.ModEq.mul_right ((k : ℕ)) (Nat.mod_modEq ((j : ℕ) + 1) 9)
    rw [show ((j : ℕ) + 1) * (k : ℕ) = (j : ℕ) * (k : ℕ) + (k : ℕ) from by ring] at h
    exact h
  have e2 : Vm (j - 1) k = om ^ ((j : ℕ) * (k : ℕ)) * om ^ (8 * (k : ℕ)) := by
    simp only [Vm, h2, ← pow_add]
    refine om_pow_congr ?_
    have h := Nat.ModEq.mul_right ((k : ℕ)) (Nat.mod_modEq ((j : ℕ) + 8) 9)
    rw [show ((j : ℕ) + 8) * (k : ℕ) = (j : ℕ) * (k : ℕ) + 8 * (k : ℕ) from by ring] at h
    exact h
  rw [e1, e2, ← mul_add, om_pow_add_inv k]
  rfl

/-- **Hückel theory for C₉.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₉` factors as `∏_{k=0}^{8} (X - 2 cos (2πk/9))`, i.e. its eigenvalues are exactly
`2 cos (2πk/9)` for `k = 0, …, 8`. -/
theorem huckel_C9 :
    ((SimpleGraph.cycleGraph 9).adjMatrix ℂ).charpoly =
      ∏ k : Fin 9, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 9) : ℝ) : ℂ)) := by
  let U : (Matrix (Fin 9) (Fin 9) ℂ)ˣ := ⟨Vm, Wm, Vm_mul_Wm, Wm_mul_Vm⟩
  have hA : (SimpleGraph.cycleGraph 9).adjMatrix ℂ
      = (U : Matrix (Fin 9) (Fin 9) ℂ) * Matrix.diagonal lam *
        (↑U⁻¹ : Matrix (Fin 9) (Fin 9) ℂ) := by
    have h : (SimpleGraph.cycleGraph 9).adjMatrix ℂ * (Vm * Wm)
        = Vm * Matrix.diagonal lam * Wm := by
      rw [← Matrix.mul_assoc, adj_mul_Vm]
    simpa [Vm_mul_Wm, U] using h
  rw [hA, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
  rfl

/-- The explicit eigenvectors: `v_k (j) = exp (2πi jk / 9)`. -/
theorem huckel_C9_eigenvector (k : Fin 9) :
    ((SimpleGraph.cycleGraph 9).adjMatrix ℂ).mulVec
        (fun j : Fin 9 => Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) * (k : ℕ) / 9)) =
      ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 9) : ℝ) : ℂ) •
        (fun j : Fin 9 => Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) * (k : ℕ) / 9)) := by
  have hcol : ∀ j : Fin 9,
      Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) * (k : ℕ) / 9) = Vm j k := by
    intro j
    rw [Vm, om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  funext j
  have h := congrFun (congrFun adj_mul_Vm j) k
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hcol]
  rw [h]
  simp only [lam]
  ring

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

