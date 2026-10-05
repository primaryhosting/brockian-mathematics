/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The adjacency eigenvalues of the cycle graph `C_10` are exactly the numbers
`2 * cos (2 * π * k / 10)` for `k = 0, …, 9`.

We index the vertices of `C₁₀` by `ZMod 10`, so that the adjacency matrix is
`C10adj i j = 1` iff `i` and `j` differ by `1`.  The eigenvectors are the discrete
Fourier modes `j ↦ ζ (k * j)` where `ζ a = exp (2 π i a / 10)`.
-/

namespace Chem

open Finset

/-- A primitive 10-th root of unity. -/
noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

/-- The character `a ↦ exp (2 π i a / 10)` of `ZMod 10`. -/
noncomputable def zeta (a : ZMod 10) : ℂ := w ^ a.val

/-- The adjacency matrix of the cycle graph `C₁₀`, with vertices indexed by `ZMod 10`. -/
def C10adj : Matrix (ZMod 10) (ZMod 10) ℂ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

lemma isPrimitiveRoot_w : IsPrimitiveRoot w 10 := by
  have := Complex.isPrimitiveRoot_exp 10 (by norm_num)
  simpa [w] using this

lemma w_pow_ten : w ^ 10 = 1 := isPrimitiveRoot_w.pow_eq_one

lemma w_pow_mod (n : ℕ) : w ^ (n % 10) = w ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 10]
  rw [pow_add, pow_mul, w_pow_ten, one_pow, one_mul]

@[simp] lemma zeta_zero : zeta 0 = 1 := by simp [zeta]

lemma zeta_add (a b : ZMod 10) : zeta (a + b) = zeta a * zeta b := by
  rw [zeta, zeta, zeta, ZMod.val_add, w_pow_mod, pow_add]

lemma zeta_eq_one_iff (a : ZMod 10) : zeta a = 1 ↔ a = 0 := by
  rw [zeta, isPrimitiveRoot_w.pow_eq_one_iff_dvd]
  constructor
  · intro h
    exact (ZMod.val_eq_zero a).mp (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt a))
  · rintro rfl
    simp

lemma zeta_ne_zero (a : ZMod 10) : zeta a ≠ 0 := by
  rw [zeta]
  exact pow_ne_zero _ (Complex.exp_ne_zero _)

lemma zeta_mul_neg (a : ZMod 10) : zeta a * zeta (-a) = 1 := by
  rw [← zeta_add]; simp

/-- Orthogonality of the characters of `ZMod 10`. -/
lemma sum_zeta (a : ZMod 10) : ∑ k : ZMod 10, zeta (k * a) = if a = 0 then 10 else 0 := by
  by_cases ha : a = 0
  · subst ha; simp [ZMod.card]
  · simp only [ha, if_false]
    set S : ℂ := ∑ k : ZMod 10, zeta (k * a) with hS
    have hshift : zeta a * S = S := by
      rw [hS, Finset.mul_sum]
      have h : ∀ k : ZMod 10, zeta a * zeta (k * a) = zeta ((k + 1) * a) := by
        intro k
        rw [← zeta_add]
        ring_nf
      rw [Finset.sum_congr rfl fun k _ => h k]
      exact Equiv.sum_comp (Equiv.addRight (1 : ZMod 10)) (fun k => zeta (k * a))
    have h1 : zeta a ≠ 1 := fun h => ha ((zeta_eq_one_iff a).mp h)
    have hz : (zeta a - 1) * S = 0 := by rw [sub_mul, hshift, one_mul, sub_self]
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd (sub_eq_zero.mp h) h1
    · exact h

lemma mulVec_apply (v : ZMod 10 → ℂ) (i : ZMod 10) :
    C10adj.mulVec v i = v (i + 1) + v (i - 1) := by
  have hne : (i - 1 : ZMod 10) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 10) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have key : ∀ j : ZMod 10, C10adj i j * v j
      = (if j = i + 1 then v j else 0) + (if j = i - 1 then v j else 0) := by
    intro j
    have h1 : (i - j = 1) ↔ (j = i - 1) := by
      constructor
      · intro h; rw [← h]; ring
      · intro h; rw [h]; ring
    have h2 : (j - i = 1) ↔ (j = i + 1) := by
      constructor
      · intro h; rw [← h]; ring
      · intro h; rw [h]; ring
    by_cases hb : j = i + 1
    · subst hb
      have hA : C10adj i (i + 1) = 1 := by
        simp only [C10adj, Matrix.of_apply]
        rw [if_pos]
        right; ring
      rw [hA, one_mul, if_pos rfl, if_neg (fun h => hne h.symm), add_zero]
    · by_cases hc : j = i - 1
      · subst hc
        have hA : C10adj i (i - 1) = 1 := by
          simp only [C10adj, Matrix.of_apply]
          rw [if_pos]
          left; ring
        rw [hA, one_mul, if_neg hb, if_pos rfl, zero_add]
      · have hA : C10adj i j = 0 := by
          simp only [C10adj, Matrix.of_apply]
          rw [if_neg]
          rintro (h | h)
          · exact hc (h1.mp h)
          · exact hb (h2.mp h)
        rw [hA, zero_mul, if_neg hb, if_neg hc, add_zero]
  rw [Matrix.mulVec, dotProduct]
  simp only [key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-- The eigenvalue attached to the `k`-th Fourier mode. -/
lemma zeta_add_zeta_neg (k : ZMod 10) :
    zeta k + zeta (-k) = ((2 * Real.cos (2 * Real.pi * k.val / 10) : ℝ) : ℂ) := by
  have hz : zeta k = Complex.exp ((2 * Real.pi * (k.val : ℝ) / 10 : ℝ) * Complex.I) := by
    rw [zeta, w, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz' : zeta (-k) = Complex.exp (-((2 * Real.pi * (k.val : ℝ) / 10 : ℝ) * Complex.I)) := by
    have h := zeta_mul_neg k
    have hinv : zeta (-k) = (zeta k)⁻¹ := (DivisionMonoid.inv_eq_of_mul _ _ h).symm
    rw [hinv, hz, ← Complex.exp_neg]
  have hcast : ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 10) : ℝ) : ℂ)
      = 2 * Complex.cos ((2 * Real.pi * (k.val : ℝ) / 10 : ℝ) : ℂ) := by
    push_cast [Complex.ofReal_cos]
    ring
  rw [hz, hz', hcast, Complex.cos, neg_mul]
  ring

/-- **Hückel theory for the cycle `C₁₀`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₀` if and only if `μ = 2 cos (2 π k / 10)` for some
`k ∈ {0, …, 9}`. -/
theorem huckel_C10 (μ : ℂ) :
    (∃ v : ZMod 10 → ℂ, v ≠ 0 ∧ C10adj.mulVec v = μ • v) ↔
      ∃ k : ZMod 10, μ = ((2 * Real.cos (2 * Real.pi * k.val / 10) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    have hrec : ∀ i : ZMod 10, v (i + 1) + v (i - 1) = μ * v i := by
      intro i
      have := congrFun hv i
      rwa [mulVec_apply] at this
    set c : ZMod 10 → ℂ := fun k => ∑ j : ZMod 10, zeta (-(k * j)) * v j with hc
    have hkey : ∀ k : ZMod 10, μ * c k = (zeta k + zeta (-k)) * c k := by
      intro k
      have e1 : ∑ j : ZMod 10, zeta (-(k * j)) * v (j + 1) = zeta k * c k := by
        have hE := Equiv.sum_comp (Equiv.addRight (1 : ZMod 10))
          (fun j => zeta (-(k * (j - 1))) * v j)
        simp only [Equiv.coe_addRight, add_sub_cancel_right] at hE
        have hterm : ∀ j : ZMod 10,
            zeta (-(k * (j - 1))) * v j = zeta k * (zeta (-(k * j)) * v j) := by
          intro j
          have hx : -(k * (j - 1)) = k + -(k * j) := by ring
          rw [hx, zeta_add]
          ring
        calc ∑ j : ZMod 10, zeta (-(k * j)) * v (j + 1)
            = ∑ j : ZMod 10, zeta (-(k * (j - 1))) * v j := hE
          _ = ∑ j : ZMod 10, zeta k * (zeta (-(k * j)) * v j) :=
              Finset.sum_congr rfl fun j _ => hterm j
          _ = zeta k * c k := by rw [hc, Finset.mul_sum]
      have e2 : ∑ j : ZMod 10, zeta (-(k * j)) * v (j - 1) = zeta (-k) * c k := by
        have hE := Equiv.sum_comp (Equiv.subRight (1 : ZMod 10))
          (fun j => zeta (-(k * (j + 1))) * v j)
        simp only [Equiv.subRight_apply, sub_add_cancel] at hE
        have hterm : ∀ j : ZMod 10,
            zeta (-(k * (j + 1))) * v j = zeta (-k) * (zeta (-(k * j)) * v j) := by
          intro j
          have hx : -(k * (j + 1)) = -k + -(k * j) := by ring
          rw [hx, zeta_add]
          ring
        calc ∑ j : ZMod 10, zeta (-(k * j)) * v (j - 1)
            = ∑ j : ZMod 10, zeta (-(k * (j + 1))) * v j := hE
          _ = ∑ j : ZMod 10, zeta (-k) * (zeta (-(k * j)) * v j) :=
              Finset.sum_congr rfl fun j _ => hterm j
          _ = zeta (-k) * c k := by rw [hc, Finset.mul_sum]
      calc μ * c k = ∑ j : ZMod 10, zeta (-(k * j)) * (μ * v j) := by
            rw [hc, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j : ZMod 10, (zeta (-(k * j)) * v (j + 1) + zeta (-(k * j)) * v (j - 1)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← hrec j]; ring
        _ = zeta k * c k + zeta (-k) * c k := by rw [Finset.sum_add_distrib, e1, e2]
        _ = (zeta k + zeta (-k)) * c k := by ring
    have hex : ∃ k : ZMod 10, c k ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hv0
      funext j
      have h10 : (10 : ℂ) * v j = 0 := by
        have hzero : ∑ k : ZMod 10, zeta (k * j) * c k = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          rw [hcon k, mul_zero]
        rw [← hzero]
        have expand : ∀ k : ZMod 10, zeta (k * j) * c k
            = ∑ l : ZMod 10, zeta (k * (j - l)) * v l := by
          intro k
          rw [hc, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          have hx : k * (j - l) = k * j + -(k * l) := by ring
          rw [hx, zeta_add]
          ring
        rw [Finset.sum_congr rfl fun k _ => expand k, Finset.sum_comm]
        have hinner : ∀ l : ZMod 10, ∑ k : ZMod 10, zeta (k * (j - l)) * v l
            = (if j - l = 0 then (10 : ℂ) else 0) * v l := by
          intro l
          rw [← Finset.sum_mul, sum_zeta]
        rw [Finset.sum_congr rfl fun l _ => hinner l]
        rw [Finset.sum_eq_single j]
        · simp
        · intro l _ hl
          have hjl : j - l ≠ 0 := by
            intro h
            exact hl (by linear_combination -h)
          simp [hjl]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hten : (10 : ℂ) ≠ 0 := by norm_num
      simpa [hten] using h10
    obtain ⟨k, hk⟩ := hex
    refine ⟨k, ?_⟩
    rw [← zeta_add_zeta_neg k]
    exact mul_right_cancel₀ hk (hkey k)
  · rintro ⟨k, rfl⟩
    refine ⟨fun j => zeta (k * j), ?_, ?_⟩
    · intro h
      simpa using congrFun h 0
    · funext i
      rw [mulVec_apply]
      have h1 : k * (i + 1) = k * i + k := by ring
      have h2 : k * (i - 1) = k * i + -k := by ring
      rw [h1, h2, zeta_add, zeta_add, ← zeta_add_zeta_neg k]
      simp only [Pi.smul_apply, smul_eq_mul]
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

