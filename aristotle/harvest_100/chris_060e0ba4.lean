/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset

/-- A primitive 15-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 15)

lemma zeta_primitive : IsPrimitiveRoot zeta 15 := by
  have := Complex.isPrimitiveRoot_exp 15 (by norm_num)
  simpa [zeta] using this

lemma zeta_pow_15 : zeta ^ 15 = 1 := zeta_primitive.pow_eq_one

lemma zeta_pow_mod (m : ℕ) : zeta ^ (m % 15) = zeta ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 15]
  rw [pow_add, pow_mul, zeta_pow_15, one_pow, one_mul]

/-- The character `a ↦ exp (2 π i a / 15)` on `ZMod 15`. -/
noncomputable def ee (a : ZMod 15) : ℂ := zeta ^ a.val

lemma ee_add (a b : ZMod 15) : ee (a + b) = ee a * ee b := by
  simp [ee, ZMod.val_add, zeta_pow_mod, pow_add]

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_ne_zero (a : ZMod 15) : ee a ≠ 0 := by
  have : zeta ≠ 0 := by
    intro h
    have := zeta_pow_15
    rw [h] at this
    simp at this
  exact pow_ne_zero _ this

lemma ee_mul_neg (a : ZMod 15) : ee a * ee (-a) = 1 := by
  rw [← ee_add]; simp [ee_zero]

lemma ee_ne_one {m : ZMod 15} (hm : m ≠ 0) : ee m ≠ 1 := by
  have h0 : m.val ≠ 0 := by
    simpa [ZMod.val_eq_zero_iff] using hm
  exact zeta_primitive.pow_ne_one_of_pos_of_lt (Nat.pos_of_ne_zero h0) m.val_lt

lemma ee_sum (m : ZMod 15) : ∑ k : ZMod 15, ee (k * m) = if m = 0 then 15 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp [ee_zero, ZMod.card]
  · rw [if_neg hm]
    have hshift : ∑ k : ZMod 15, ee ((k + 1) * m) = ∑ k : ZMod 15, ee (k * m) :=
      Equiv.sum_comp (Equiv.addRight (1 : ZMod 15)) (fun k => ee (k * m))
    have hexp : ∀ k : ZMod 15, ee ((k + 1) * m) = ee (k * m) * ee m := by
      intro k
      rw [← ee_add]; ring_nf
    rw [Finset.sum_congr rfl (fun k _ => hexp k), ← Finset.sum_mul] at hshift
    have : (∑ k : ZMod 15, ee (k * m)) * (ee m - 1) = 0 := by
      rw [mul_sub, mul_one, hshift, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (by linear_combination h) (ee_ne_one hm)

lemma ee_add_ee_neg (k : ZMod 15) :
    ee k + ee (-k) = 2 * Real.cos (2 * Real.pi * k.val / 15) := by
  set θ : ℝ := 2 * Real.pi * k.val / 15 with hθ
  have h1 : ee k = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [ee, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast [hθ]
    ring
  have h2 : ee (-k) = Complex.exp (-((θ : ℂ) * Complex.I)) := by
    have hmul := ee_mul_neg k
    rw [h1] at hmul
    have hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    field_simp [Complex.exp_neg]
    linear_combination hmul
  rw [h1, h2, Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I]
  simp [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
  ring

/-- The adjacency matrix of the cycle graph `C₁₅`, with vertices indexed by `ZMod 15`. -/
noncomputable def C15adj : Matrix (ZMod 15) (ZMod 15) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

lemma C15adj_mulVec (v : ZMod 15 → ℂ) (i : ZMod 15) :
    (C15adj *ᵥ v) i = v (i + 1) + v (i - 1) := by
  have hsplit : ∀ j : ZMod 15,
      C15adj i j * v j = (if j = i + 1 then v j else 0) + (if j = i - 1 then v j else 0) := by
    intro j
    by_cases h1 : j = i + 1 <;> by_cases h2 : j = i - 1 <;>
      simp [C15adj, h1, h2]
    · exfalso
      have : (i : ZMod 15) + 1 = i - 1 := by rw [← h1, h2]
      have h3 : (2 : ZMod 15) = 0 := by linear_combination this
      exact absurd h3 (by decide)
  rw [Matrix.mulVec, Matrix.dotProduct]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i + 1) v, Finset.sum_ite_eq' Finset.univ (i - 1) v]
  simp

/-- **Hückel theory for the cycle `C₁₅`**: a complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph on 15 vertices if and only if it is of the form
`2 cos (2 π k / 15)` for some `k ∈ {0, …, 14}`. -/
theorem huckel_C15 (μ : ℂ) :
    (∃ v : ZMod 15 → ℂ, v ≠ 0 ∧ C15adj *ᵥ v = μ • v) ↔
      ∃ k : Fin 15, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) := by
  constructor
  · rintro ⟨v, hv, hA⟩
    have hrec : ∀ i, v (i + 1) + v (i - 1) = μ * v i := by
      intro i
      have h := congrFun hA i
      rwa [C15adj_mulVec, Pi.smul_apply, smul_eq_mul] at h
    set c : ZMod 15 → ℂ := fun k => ∑ j, v j * ee (-(k * j)) with hc
    have hinv : ∀ j, ∑ k, c k * ee (k * j) = 15 * v j := by
      intro j
      have step1 : ∀ k : ZMod 15, c k * ee (k * j) = ∑ j', v j' * ee (k * (j - j')) := by
        intro k
        rw [hc]
        simp only [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [mul_assoc, ← ee_add]
        ring_nf
      have step2 : ∀ j' : ZMod 15,
          ∑ k : ZMod 15, v j' * ee (k * (j - j')) = if j' = j then 15 * v j else 0 := by
        intro j'
        rw [← Finset.mul_sum, ee_sum]
        by_cases h : j' = j
        · subst h; simp [mul_comm]
        · rw [if_neg (by simpa [sub_eq_zero] using fun hh => h hh.symm), if_neg h, mul_zero]
      rw [Finset.sum_congr rfl (fun k _ => step1 k), Finset.sum_comm,
        Finset.sum_congr rfl (fun j' _ => step2 j'), Finset.sum_ite_eq' Finset.univ j]
      simp
    have hB : ∀ k : ZMod 15, μ * c k = (ee k + ee (-k)) * c k := by
      intro k
      have h1 : ∑ j : ZMod 15, v (j + 1) * ee (-(k * j)) = ee k * c k := by
        have e1 : ∀ j : ZMod 15,
            v (j + 1) * ee (-(k * j)) = (fun j' => v j' * ee (-(k * (j' - 1)))) (j + 1) := by
          intro j; simp
        rw [Finset.sum_congr rfl fun j _ => e1 j,
          Equiv.sum_comp (Equiv.addRight (1 : ZMod 15)) (fun j' => v j' * ee (-(k * (j' - 1))))]
        rw [hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have : -(k * (j - 1)) = k + -(k * j) := by ring
        rw [this, ee_add]
        ring
      have h2 : ∑ j : ZMod 15, v (j - 1) * ee (-(k * j)) = ee (-k) * c k := by
        have e1 : ∀ j : ZMod 15,
            v (j - 1) * ee (-(k * j)) = (fun j' => v j' * ee (-(k * (j' + 1)))) (j - 1) := by
          intro j; simp
        rw [Finset.sum_congr rfl fun j _ => e1 j,
          Equiv.sum_comp (Equiv.subRight (1 : ZMod 15)) (fun j' => v j' * ee (-(k * (j' + 1))))]
        rw [hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have : -(k * (j + 1)) = -k + -(k * j) := by ring
        rw [this, ee_add]
        ring
      calc μ * c k = ∑ j : ZMod 15, (μ * v j) * ee (-(k * j)) := by
            rw [hc, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j : ZMod 15, (v (j + 1) * ee (-(k * j)) + v (j - 1) * ee (-(k * j))) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← hrec j]; ring
        _ = ee k * c k + ee (-k) * c k := by rw [Finset.sum_add_distrib, h1, h2]
        _ = (ee k + ee (-k)) * c k := by ring
    obtain ⟨j0, hj0⟩ : ∃ j, v j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (funext fun j => by simpa using h j)
    have hcne : ∃ k, c k ≠ 0 := by
      by_contra h
      push_neg at h
      have := hinv j0
      rw [Finset.sum_congr rfl (fun k _ => by rw [h k, zero_mul] : ∀ k ∈ Finset.univ,
        c k * ee (k * j0) = 0)] at this
      simp at this
      exact hj0 this
    obtain ⟨k, hk⟩ := hcne
    refine ⟨⟨k.val, k.val_lt⟩, ?_⟩
    have hμ : μ = ee k + ee (-k) := by
      have := hB k
      field_simp at this
      rcases mul_right_cancel₀ hk this with h
      exact h
    rw [hμ, ee_add_ee_neg k]
    norm_num
  · rintro ⟨k, rfl⟩
    set K : ZMod 15 := (k : ℕ) with hK
    have hKval : K.val = (k : ℕ) := ZMod.val_natCast_of_lt k.isLt
    refine ⟨fun j => ee (K * j), ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp [ee_zero] at this
    · funext i
      rw [C15adj_mulVec, Pi.smul_apply, smul_eq_mul]
      have e1 : K * (i + 1) = K * i + K := by ring
      have e2 : K * (i - 1) = K * i + -K := by ring
      rw [e1, e2, ee_add, ee_add, ← hKval, ← ee_add_ee_neg K]
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

