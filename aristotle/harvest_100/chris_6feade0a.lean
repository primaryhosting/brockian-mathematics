/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 14)

lemma om_primitive : IsPrimitiveRoot om 14 := by
  have h := Complex.isPrimitiveRoot_exp 14 (by norm_num)
  simpa [om] using h

lemma om_pow_14 : om ^ 14 = 1 := om_primitive.pow_eq_one

lemma om_pow_mod (n : ℕ) : om ^ (n % 14) = om ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 14]
  rw [pow_add, pow_mul, om_pow_14, one_pow, one_mul]

/-- The standard additive character of `ZMod 14` into `ℂ`. -/
noncomputable def ch (a : ZMod 14) : ℂ := om ^ a.val

lemma ch_zero : ch 0 = 1 := by simp [ch]

lemma ch_ne_zero (a : ZMod 14) : ch a ≠ 0 := by
  simp only [ch, om]
  exact pow_ne_zero _ (Complex.exp_ne_zero _)

lemma ch_add (a b : ZMod 14) : ch (a + b) = ch a * ch b := by
  simp only [ch, ZMod.val_add, om_pow_mod, pow_add]

lemma ch_mul_neg (a : ZMod 14) : ch a * ch (-a) = 1 := by
  rw [← ch_add, add_neg_cancel, ch_zero]

lemma ch_eq_one_iff (a : ZMod 14) : ch a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have hd : (14 : ℕ) ∣ a.val := (om_primitive.pow_eq_one_iff_dvd a.val).1 h
    have hlt : a.val < 14 := ZMod.val_lt a
    have hv : a.val = 0 := by rcases hd with ⟨c, hc⟩; omega
    exact (ZMod.val_eq_zero a).1 hv
  · rintro rfl; exact ch_zero

/-- Shifting the summation index over `ZMod 14` does not change the sum. -/
lemma sum_shift (g : ZMod 14 → ℂ) (c : ZMod 14) : ∑ j : ZMod 14, g (j + c) = ∑ j, g j :=
  Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)

/-- Orthogonality / geometric sum for the character `ch`. -/
lemma sum_ch (c : ZMod 14) :
    ∑ j : ZMod 14, ch (c * j) = if c = 0 then 14 else 0 := by
  by_cases hc : c = 0
  · subst hc; simp [ch_zero]
  · simp only [hc, if_false]
    set S := ∑ j : ZMod 14, ch (c * j) with hS
    have hshift : ch c * S = S := by
      rw [hS, Finset.mul_sum]
      have key : ∀ j : ZMod 14, ch c * ch (c * j) = (fun i : ZMod 14 => ch (c * i)) (j + 1) := by
        intro j
        simp only [mul_add, mul_one, ch_add]
        ring
      rw [Finset.sum_congr rfl (fun j _ => key j)]
      exact sum_shift (fun i : ZMod 14 => ch (c * i)) 1
    have h1 : (ch c - 1) * S = 0 := by
      rw [sub_mul, one_mul, hshift, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (by linear_combination h : ch c = 1) (fun hh => hc ((ch_eq_one_iff c).1 hh))
    · exact h

/-- The adjacency matrix of the cycle graph `C₁₄`, with vertices indexed by `ZMod 14`. -/
def C14adj : Matrix (ZMod 14) (ZMod 14) ℂ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

lemma C14adj_apply (i j : ZMod 14) :
    C14adj i j = (if j = i + 1 then (1 : ℂ) else 0) + (if j = i - 1 then 1 else 0) := by
  have hne : (i + 1 : ZMod 14) ≠ i - 1 := by
    intro h
    have : (1 : ZMod 14) = -1 := by linear_combination h
    exact absurd this (by decide)
  unfold C14adj
  by_cases h1 : j = i + 1 <;> by_cases h2 : j = i - 1 <;> simp [h1, h2] at * <;> tauto

lemma C14adj_mulVec (v : ZMod 14 → ℂ) (i : ZMod 14) :
    C14adj.mulVec v i = v (i + 1) + v (i - 1) := by
  simp only [Matrix.mulVec, dotProduct, C14adj_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq' Finset.univ (i + 1) v,
    Finset.sum_ite_eq' Finset.univ (i - 1) v, Finset.mem_univ, if_true]

/-- The `k`-th Fourier coefficient of an eigenvector can only be nonzero when the
eigenvalue equals `ch k + ch (-k)`. -/
lemma ch_sum_eigen (μ : ℂ) (v : ZMod 14 → ℂ) (hv : C14adj.mulVec v = μ • v) (k : ZMod 14) :
    (μ - (ch k + ch (-k))) * (∑ j : ZMod 14, v j * ch (-(k * j))) = 0 := by
  set w := ∑ j : ZMod 14, v j * ch (-(k * j)) with hw
  have hvj : ∀ j, v (j + 1) + v (j - 1) = μ * v j := by
    intro j
    have h := congrFun hv j
    rw [C14adj_mulVec] at h
    simpa using h
  have h1 : ∑ j : ZMod 14, v (j + 1) * ch (-(k * j)) = ch k * w := by
    have key : ∀ j : ZMod 14, v (j + 1) * ch (-(k * j))
        = ch k * (v (j + 1) * ch (-(k * (j + 1)))) := by
      intro j
      have hex : (-(k * (j + 1)) : ZMod 14) = -(k * j) + -k := by ring
      rw [hex, ch_add]
      linear_combination (-(v (j + 1) * ch (-(k * j)))) * ch_mul_neg k
    calc ∑ j : ZMod 14, v (j + 1) * ch (-(k * j))
        = ∑ j : ZMod 14, (fun i : ZMod 14 => ch k * (v i * ch (-(k * i)))) (j + 1) :=
          Finset.sum_congr rfl (fun j _ => key j)
      _ = ∑ i : ZMod 14, ch k * (v i * ch (-(k * i))) :=
          sum_shift (fun i : ZMod 14 => ch k * (v i * ch (-(k * i)))) 1
      _ = ch k * w := by rw [hw, Finset.mul_sum]
  have h2 : ∑ j : ZMod 14, v (j - 1) * ch (-(k * j)) = ch (-k) * w := by
    have key : ∀ j : ZMod 14, v (j - 1) * ch (-(k * j))
        = ch (-k) * (v (j + -1) * ch (-(k * (j + -1)))) := by
      intro j
      have hex : (-(k * (j + -1)) : ZMod 14) = -(k * j) + k := by ring
      have hj : (j + -1 : ZMod 14) = j - 1 := by ring
      rw [hex, hj, ch_add]
      linear_combination (-(v (j - 1) * ch (-(k * j)))) * ch_mul_neg k
    calc ∑ j : ZMod 14, v (j - 1) * ch (-(k * j))
        = ∑ j : ZMod 14, (fun i : ZMod 14 => ch (-k) * (v i * ch (-(k * i)))) (j + -1) :=
          Finset.sum_congr rfl (fun j _ => key j)
      _ = ∑ i : ZMod 14, ch (-k) * (v i * ch (-(k * i))) :=
          sum_shift (fun i : ZMod 14 => ch (-k) * (v i * ch (-(k * i)))) (-1)
      _ = ch (-k) * w := by rw [hw, Finset.mul_sum]
  have hmain : μ * w = (ch k + ch (-k)) * w := by
    calc μ * w = ∑ j : ZMod 14, (μ * v j) * ch (-(k * j)) := by
          rw [hw, Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = ∑ j : ZMod 14, (v (j + 1) + v (j - 1)) * ch (-(k * j)) := by
          exact Finset.sum_congr rfl (fun j _ => by rw [hvj j])
      _ = (∑ j : ZMod 14, v (j + 1) * ch (-(k * j)))
            + ∑ j : ZMod 14, v (j - 1) * ch (-(k * j)) := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = (ch k + ch (-k)) * w := by rw [h1, h2]; ring
  linear_combination hmain

/-- Fourier inversion: if all Fourier coefficients vanish, the vector vanishes. -/
lemma eq_zero_of_fourier_zero (v : ZMod 14 → ℂ)
    (h : ∀ k : ZMod 14, ∑ j : ZMod 14, v j * ch (-(k * j)) = 0) : v = 0 := by
  funext i
  have key : ∑ k : ZMod 14, (∑ j : ZMod 14, v j * ch (-(k * j))) * ch (k * i)
      = 14 * v i := by
    have step : ∀ k : ZMod 14, (∑ j : ZMod 14, v j * ch (-(k * j))) * ch (k * i)
        = ∑ j : ZMod 14, v j * ch ((i - j) * k) := by
      intro k
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_assoc, ← ch_add]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun k _ => step k), Finset.sum_comm]
    have inner : ∀ j : ZMod 14, ∑ k : ZMod 14, v j * ch ((i - j) * k)
        = if j = i then 14 * v j else 0 := by
      intro j
      rw [← Finset.mul_sum, sum_ch]
      by_cases hj : j = i
      · subst hj; simp [mul_comm]
      · have hij : i - j ≠ 0 := fun hc => hj (by linear_combination -hc)
        simp [hij, hj]
    rw [Finset.sum_congr rfl (fun j _ => inner j)]
    simp
  rw [Finset.sum_congr rfl (fun k _ => by rw [h k, zero_mul])] at key
  simp only [Finset.sum_const_zero] at key
  have h14 : (14 : ℂ) * v i = 0 := key.symm
  have hvi : v i = 0 := by
    rcases mul_eq_zero.1 h14 with h' | h'
    · norm_num at h'
    · exact h'
  simpa using hvi

lemma ch_add_ch_neg (k : ZMod 14) :
    ch k + ch (-k) = ((2 * Real.cos (2 * Real.pi * k.val / 14) : ℝ) : ℂ) := by
  set t : ℂ := ((2 * Real.pi * k.val / 14 : ℝ) : ℂ) with ht
  have hchk : ch k = Complex.exp (t * Complex.I) := by
    rw [ch, om, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have h2 : ch (-k) = (ch k)⁻¹ := (inv_eq_of_mul_eq_one_right (ch_mul_neg k)).symm
  rw [h2, hchk, ← Complex.exp_neg,
    show -(t * Complex.I) = -t * Complex.I by ring, ← Complex.two_cos, ht]
  push_cast
  ring

/-- **Hückel theory for the C₁₄ annulene ring.**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₁₄`
(the Hückel matrix in units where `α = 0` and `β = 1`) if and only if
`μ = 2 cos (2 π k / 14)` for some `k ∈ {0, 1, …, 13}`. -/
theorem huckel_C14 (μ : ℂ) :
    (∃ v : ZMod 14 → ℂ, v ≠ 0 ∧ C14adj.mulVec v = μ • v) ↔
      ∃ k : ℕ, k < 14 ∧ μ = ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    by_contra hcon
    push_neg at hcon
    have hall : ∀ k : ZMod 14, ∑ j : ZMod 14, v j * ch (-(k * j)) = 0 := by
      intro k
      rcases mul_eq_zero.1 (ch_sum_eigen μ v hv k) with h | h
      · exfalso
        have hmu : μ = ch k + ch (-k) := by linear_combination h
        rw [ch_add_ch_neg k] at hmu
        exact hcon k.val (ZMod.val_lt k) (by exact_mod_cast hmu)
      · exact h
    exact hv0 (eq_zero_of_fourier_zero v hall)
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun j => ch ((k : ZMod 14) * j), ?_, ?_⟩
    · intro hzero
      have h0 := congrFun hzero 0
      simp [ch_zero] at h0
    · funext i
      rw [C14adj_mulVec]
      have e1 : ch ((k : ZMod 14) * (i + 1)) = ch ((k : ZMod 14) * i) * ch (k : ZMod 14) := by
        rw [show ((k : ZMod 14) * (i + 1)) = (k : ZMod 14) * i + (k : ZMod 14) by ring, ch_add]
      have e2 : ch ((k : ZMod 14) * (i - 1)) = ch ((k : ZMod 14) * i) * ch (-(k : ZMod 14)) := by
        rw [show ((k : ZMod 14) * (i - 1)) = (k : ZMod 14) * i + -(k : ZMod 14) by ring, ch_add]
      have hval : ((k : ZMod 14)).val = k := by
        simpa using ZMod.val_natCast_of_lt hk
      have hsum : ch (k : ZMod 14) + ch (-(k : ZMod 14))
          = ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ) := by
        rw [ch_add_ch_neg, hval]
      simp only [Pi.smul_apply, smul_eq_mul, e1, e2]
      rw [← mul_add, hsum]
      ring

/-- Restatement in terms of `Module.End.HasEigenvalue` for the linear map `Matrix.toLin'`. -/
theorem huckel_C14_hasEigenvalue_iff (μ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' C14adj : Module.End ℂ (ZMod 14 → ℂ)) μ ↔
      ∃ k : ℕ, k < 14 ∧ μ = ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ) := by
  rw [← huckel_C14]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    refine ⟨v, hv.2, ?_⟩
    have := Module.End.mem_eigenspace_iff.1 hv.1
    simpa [Matrix.toLin'_apply] using this
  · rintro ⟨v, hv0, hv⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector
      (x := v) ⟨Module.End.mem_eigenspace_iff.2 ?_, hv0⟩
    simpa [Matrix.toLin'_apply] using hv

/-- The set of eigenvalues of the `C₁₄` adjacency matrix is exactly
`{2 cos (2 π k / 14) : k = 0, …, 13}`. -/
theorem huckel_C14_eigenvalue_set :
    {μ : ℂ | ∃ v : ZMod 14 → ℂ, v ≠ 0 ∧ C14adj.mulVec v = μ • v}
      = Set.range (fun k : Fin 14 => ((2 * Real.cos (2 * Real.pi * k.val / 14) : ℝ) : ℂ)) := by
  ext μ
  rw [Set.mem_setOf_eq, huckel_C14]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, k.isLt, rfl⟩

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

