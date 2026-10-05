import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Matrix

namespace Chem

/-- A primitive 19-th root of unity. -/
noncomputable def omega19 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 19)

lemma isPrimitiveRoot_omega19 : IsPrimitiveRoot omega19 19 := by
  simpa [omega19] using Complex.isPrimitiveRoot_exp 19 (by norm_num)

lemma omega19_pow : omega19 ^ 19 = 1 := isPrimitiveRoot_omega19.pow_eq_one

lemma omega19_ne_zero : omega19 ≠ 0 := by
  intro h
  have := omega19_pow
  rw [h] at this
  norm_num at this

/-- The discrete Fourier transform matrix of size 19. -/
noncomputable def F19 : Matrix (Fin 19) (Fin 19) ℂ :=
  Matrix.of fun i j => omega19 ^ (i.val * j.val)

/-- The inverse discrete Fourier transform matrix of size 19. -/
noncomputable def G19 : Matrix (Fin 19) (Fin 19) ℂ :=
  Matrix.of fun j k => (19 : ℂ)⁻¹ * (omega19⁻¹) ^ (j.val * k.val)

/-- The `k`-th Hückel eigenvalue of the cycle `C₁₉`. -/
noncomputable def hueckelEigenvalue (k : Fin 19) : ℂ :=
  ((2 * Real.cos (2 * Real.pi * k.val / 19) : ℝ) : ℂ)

/-- The diagonal matrix of Hückel eigenvalues. -/
noncomputable def D19 : Matrix (Fin 19) (Fin 19) ℂ := Matrix.diagonal hueckelEigenvalue

lemma sum_pow_val (z : ℂ) (hz : z ^ 19 = 1) :
    ∑ j : Fin 19, z ^ (j : ℕ) = if z = 1 then (19 : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => z ^ j) 19]
  by_cases h : z = 1
  · simp [h]
  · rw [geom_sum_eq h, hz, sub_self, zero_div, if_neg h]

lemma pow_pow_19 (v : ℂ) (hv : v ^ 19 = 1) (a : ℕ) : (v ^ a) ^ 19 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hv, one_pow]

lemma F_mul_G : F19 * G19 = 1 := by
  ext i k
  rw [Matrix.mul_apply]
  set z : ℂ := omega19 ^ i.val * (omega19 ^ k.val)⁻¹ with hzdef
  have hterm : ∀ j : Fin 19, F19 i j * G19 j k = (19 : ℂ)⁻¹ * z ^ (j : ℕ) := by
    intro j
    simp only [F19, G19, Matrix.of_apply, hzdef]
    rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm k.val j.val]
    ring
  have hz19 : z ^ 19 = 1 := by
    have hwi : (omega19⁻¹) ^ 19 = 1 := by rw [inv_pow, omega19_pow, inv_one]
    rw [hzdef, ← inv_pow, mul_pow, pow_pow_19 _ omega19_pow, pow_pow_19 _ hwi, one_mul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, sum_pow_val z hz19]
  by_cases hik : i = k
  · subst hik
    have hz1 : z = 1 := by
      rw [hzdef, mul_inv_cancel₀ (pow_ne_zero _ omega19_ne_zero)]
    rw [if_pos hz1, Matrix.one_apply_eq]
    field_simp
  · have hz1 : z ≠ 1 := by
      intro h
      rw [hzdef, mul_inv_eq_one₀ (pow_ne_zero _ omega19_ne_zero)] at h
      exact hik (Fin.ext (isPrimitiveRoot_omega19.pow_inj i.isLt k.isLt h))
    rw [if_neg hz1, mul_zero, Matrix.one_apply_ne hik]

lemma G_mul_F : G19 * F19 = 1 := mul_eq_one_comm.mp F_mul_G

/-- `F19` viewed as a unit of the matrix ring. -/
noncomputable def U19 : (Matrix (Fin 19) (Fin 19) ℂ)ˣ := ⟨F19, G19, F_mul_G, G_mul_F⟩

lemma pow_val_succ (w : ℂ) (hw : w ^ 19 = 1) (i : Fin 19) :
    w ^ ((i + 1 : Fin 19) : ℕ) = w ^ (i : ℕ) * w := by
  have hval : ((i + 1 : Fin 19) : ℕ) = (i.val + 1) % 19 := by
    simp [Fin.val_add]
  have hmod : w ^ ((i.val + 1) % 19) = w ^ (i.val + 1) := by
    conv_rhs => rw [← Nat.div_add_mod (i.val + 1) 19]
    rw [pow_add, pow_mul, hw, one_pow, one_mul]
  rw [hval, hmod, pow_succ]

lemma pow_val_pred (w : ℂ) (hw : w ^ 19 = 1) (hw0 : w ≠ 0) (i : Fin 19) :
    w ^ ((i - 1 : Fin 19) : ℕ) = w ^ (i : ℕ) * w⁻¹ := by
  have h := pow_val_succ w hw (i - 1)
  rw [sub_add_cancel] at h
  rw [h, mul_assoc, mul_inv_cancel₀ hw0, mul_one]

lemma omega_pow_add_inv (k : Fin 19) :
    omega19 ^ (k : ℕ) + (omega19 ^ (k : ℕ))⁻¹ = hueckelEigenvalue k := by
  have hexp : omega19 ^ (k : ℕ) = Complex.exp ((2 * Real.pi * (k : ℕ) / 19 : ℝ) * Complex.I) := by
    rw [omega19, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hinv : (omega19 ^ (k : ℕ))⁻¹ =
      Complex.exp (-(2 * Real.pi * (k : ℕ) / 19 : ℝ) * Complex.I) := by
    rw [hexp, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [hinv, hexp, ← Complex.two_cos, hueckelEigenvalue, Complex.ofReal_mul, Complex.ofReal_cos]
  push_cast
  ring

lemma adj_mul_F : (SimpleGraph.cycleGraph 19).adjMatrix ℂ * F19 = F19 * D19 := by
  ext i k
  have hLHS : ((SimpleGraph.cycleGraph 19).adjMatrix ℂ * F19) i k
      = ∑ j ∈ (SimpleGraph.cycleGraph 19).neighborFinset i, F19 j k := by
    rw [Matrix.mul_apply]
    have := SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (SimpleGraph.cycleGraph 19) i
      (fun j => F19 j k)
    simpa [Matrix.mulVec, dotProduct] using this
  have hnb : (SimpleGraph.cycleGraph 19).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 17) (v := i)
  have hne : (i - 1 : Fin 19) ≠ i + 1 := by
    intro h
    rw [sub_eq_add_neg, add_right_inj] at h
    exact absurd h (by decide)
  rw [hLHS, hnb, Finset.sum_pair hne]
  simp only [D19]
  rw [Matrix.mul_diagonal]
  set w : ℂ := omega19 ^ (k : ℕ) with hw
  have hw19 : w ^ 19 = 1 := by
    rw [hw]
    exact pow_pow_19 _ omega19_pow _
  have hw0 : w ≠ 0 := pow_ne_zero _ omega19_ne_zero
  have hF : ∀ j : Fin 19, F19 j k = w ^ (j : ℕ) := by
    intro j
    simp only [F19, Matrix.of_apply, hw, pow_mul']
  rw [hF, hF, hF, pow_val_pred w hw19 hw0, pow_val_succ w hw19, ← omega_pow_add_inv k, ← hw]
  ring

theorem adj_eq_conj : (SimpleGraph.cycleGraph 19).adjMatrix ℂ =
    (U19 : Matrix (Fin 19) (Fin 19) ℂ) * D19 * ((U19⁻¹ : (Matrix (Fin 19) (Fin 19) ℂ)ˣ) :
      Matrix (Fin 19) (Fin 19) ℂ) := by
  have h1 : ((U19 : (Matrix (Fin 19) (Fin 19) ℂ)ˣ) : Matrix (Fin 19) (Fin 19) ℂ) = F19 := rfl
  have h2 : ((U19⁻¹ : (Matrix (Fin 19) (Fin 19) ℂ)ˣ) : Matrix (Fin 19) (Fin 19) ℂ) = G19 := rfl
  rw [h1, h2, ← adj_mul_F, mul_assoc, F_mul_G, mul_one]

/-- **Hückel theory for the cycle `C₁₉`.**  The eigenvalues of the adjacency matrix of the
cycle graph on 19 vertices are exactly the numbers `2 * cos (2 * π * k / 19)`, `k = 0, …, 18`. -/
theorem huckel_C19 :
    spectrum ℂ ((SimpleGraph.cycleGraph 19).adjMatrix ℂ) =
      {x : ℂ | ∃ k : Fin 19, x = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ)} := by
  rw [adj_eq_conj, spectrum.units_conjugate, D19, spectrum_diagonal]
  ext x
  simp [hueckelEigenvalue, eq_comm]

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

