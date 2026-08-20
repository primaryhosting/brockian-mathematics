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

namespace Frontier

section Mixing

variable {V : Type*} [Fintype V]

/-- The bilinear form associated with a weight matrix `A : V → V → ℝ`. -/

lemma bil_le_mul_sqrt (A : V → V → ℝ) (lam : ℝ) (hsymm : ∀ u v, A u v = A v u)
    (hlam : ∀ f : V → ℝ, ∑ v, f v = 0 → |bil A f f| ≤ lam * ∑ v, (f v) ^ 2)
    (f g : V → ℝ) (hf : ∑ v, f v = 0) (hg : ∑ v, g v = 0) :
    |bil A f g| ≤ lam * Real.sqrt (∑ v, (f v) ^ 2) * Real.sqrt (∑ v, (g v) ^ 2) := by
  set a : ℝ := ∑ v, (f v) ^ 2 with ha
  set b : ℝ := ∑ v, (g v) ^ 2 with hb
  have ha0 : 0 ≤ a := Finset.sum_nonneg (fun v _ => sq_nonneg _)
  have hb0 : 0 ≤ b := Finset.sum_nonneg (fun v _ => sq_nonneg _)
  rcases eq_or_lt_of_le ha0 with ha' | ha'
  · -- a = 0 forces f = 0
    have hf0 : ∀ v, f v = 0 := by
      intro v
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun v (_ : v ∈ (Finset.univ : Finset V)) =>
        sq_nonneg (f v))).1 (ha.symm.trans ha'.symm) v (Finset.mem_univ v)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have : bil A f g = 0 := by
      unfold bil
      refine Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ => ?_))
      rw [hf0 u]; ring
    rw [this, ← ha']
    simp
  rcases eq_or_lt_of_le hb0 with hb' | hb'
  · have hg0 : ∀ v, g v = 0 := by
      intro v
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun v (_ : v ∈ (Finset.univ : Finset V)) =>
        sq_nonneg (g v))).1 (hb.symm.trans hb'.symm) v (Finset.mem_univ v)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have : bil A f g = 0 := by
      unfold bil
      refine Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ => ?_))
      rw [hg0 v]; ring
    rw [this, ← hb']
    simp
  · have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha'
    have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb'
    set c : ℝ := Real.sqrt (Real.sqrt b / Real.sqrt a) with hc
    have hc0 : 0 < c := Real.sqrt_pos.2 (div_pos hsb hsa)
    have hc2 : c ^ 2 = Real.sqrt b / Real.sqrt a := by
      rw [hc, Real.sq_sqrt (le_of_lt (div_pos hsb hsa))]
    have key := bil_le_half A lam hsymm hlam (fun x => c * f x) (fun x => c⁻¹ * g x)
      (by rw [← Finset.mul_sum, hf]; ring) (by rw [← Finset.mul_sum, hg]; ring)
    rw [bil_smul_left, bil_smul_right] at key
    have hnorm1 : ∑ v, ((fun x => c * f x) v) ^ 2 = c ^ 2 * a := by
      rw [ha, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    have hnorm2 : ∑ v, ((fun x => c⁻¹ * g x) v) ^ 2 = (c⁻¹) ^ 2 * b := by
      rw [hb, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    rw [hnorm1, hnorm2] at key
    have hcc : c * (c⁻¹ * bil A f g) = bil A f g := by
      field_simp
    rw [hcc] at key
    have hsa2 : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0
    have hsb2 : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb0
    have hcinv : (c⁻¹) ^ 2 = Real.sqrt a / Real.sqrt b := by
      rw [inv_pow, hc2, inv_div]
    have hval : (c ^ 2 * a + (c⁻¹) ^ 2 * b) / 2 = Real.sqrt a * Real.sqrt b := by
      rw [hc2, hcinv]
      field_simp
      nlinarith [hsa2, hsb2]
    calc |bil A f g| ≤ lam * (c ^ 2 * a + (c⁻¹) ^ 2 * b) / 2 := key
      _ = lam * ((c ^ 2 * a + (c⁻¹) ^ 2 * b) / 2) := by ring
      _ = lam * Real.sqrt a * Real.sqrt b := by rw [hval]; ring

