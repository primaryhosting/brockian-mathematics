import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- Adjacency matrix of the cycle graph `C₇`, with vertices indexed by `ZMod 7`:
vertex `i` is adjacent to `i + 1` and to `i - 1`. -/
def C7adj : Matrix (ZMod 7) (ZMod 7) ℂ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- A primitive 7th root of unity. -/
noncomputable def zeta7 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)

lemma zeta7_isPrimitiveRoot : IsPrimitiveRoot zeta7 7 :=
  Complex.isPrimitiveRoot_exp 7 (by norm_num)

lemma zeta7_pow_seven : zeta7 ^ 7 = 1 := zeta7_isPrimitiveRoot.pow_eq_one

/-- Multiplication of a vector by the adjacency matrix of `C₇` is the discrete Laplacian-type
sum of the two neighbouring entries. -/
lemma C7adj_mulVec (v : ZMod 7 → ℂ) (i : ZMod 7) :
    (C7adj.mulVec v) i = v (i + 1) + v (i - 1) := by
  have hne : (i + 1) ≠ (i - 1) := by
    intro h
    have h2 : (2 : ZMod 7) = 0 := by linear_combination h
    exact absurd h2 (by decide)
  have key : ∀ j : ZMod 7, C7adj i j * v j
      = (if j = i + 1 then v j else 0) + (if j = i - 1 then v j else 0) := by
    intro j
    unfold C7adj
    by_cases h1 : j = i + 1
    · by_cases h2 : j = i - 1
      · exact absurd (h1.symm.trans h2) hne
      · simp [h1, hne]
    · by_cases h2 : j = i - 1 <;> simp [h1, h2, Ne.symm hne]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (i + 1) v, Finset.sum_ite_eq' Finset.univ (i - 1) v]
  simp

/-- If `y ^ 7 = 1`, then `n ↦ y ^ n` descends to a homomorphism on `ZMod 7`. -/
lemma pow_val_add {y : ℂ} (hy : y ^ 7 = 1) (a b : ZMod 7) :
    y ^ (a + b).val = y ^ a.val * y ^ b.val := by
  have hmod : ∀ m : ℕ, y ^ (m % 7) = y ^ m := by
    intro m
    conv_rhs => rw [← Nat.div_add_mod m 7, pow_add, pow_mul, hy, one_pow, one_mul]
  rw [ZMod.val_add, hmod, pow_add]

/-- Iterating a shift relation `u (i + 1) = y * u i`. -/
lemma shift_iter {y : ℂ} {u : ZMod 7 → ℂ} (h : ∀ i, u (i + 1) = y * u i) (n : ℕ) (i : ZMod 7) :
    u (i + (n : ZMod 7)) = y ^ n * u i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : (i + ((n + 1 : ℕ) : ZMod 7)) = (i + (n : ZMod 7)) + 1 := by push_cast; ring
      rw [hstep, h, ih, pow_succ]
      ring

/-- A nonzero eigenvector of the cyclic shift has eigenvalue a 7th root of unity. -/
lemma root_of_shift {y : ℂ} {u : ZMod 7 → ℂ} (hu : u ≠ 0) (h : ∀ i, u (i + 1) = y * u i) :
    y ^ 7 = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hu (funext hc)
  have h7 := shift_iter h 7 i
  have hz : ((7 : ℕ) : ZMod 7) = 0 := by decide
  rw [hz, add_zero] at h7
  field_simp at h7
  exact h7.symm

/-- `ζ⁷ᵏ + ζ⁷⁻ᵏ = 2 cos (2πk/7)`. -/
lemma zeta7_pow_add_inv (k : ℕ) :
    zeta7 ^ k + (zeta7 ^ k)⁻¹ = 2 * Real.cos (2 * Real.pi * k / 7) := by
  rw [zeta7, ← Complex.exp_nat_mul]
  have h1 : (k : ℂ) * (2 * Real.pi * Complex.I / 7)
      = ((2 * Real.pi * k / 7 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h1, ← Complex.exp_neg, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-- Every 7th root of unity `y` satisfies `y + y⁻¹ = 2 cos (2πk/7)` for some `k < 7`. -/
lemma sum_inv_eq_two_cos {y : ℂ} (hy : y ^ 7 = 1) :
    ∃ k : ℕ, k < 7 ∧ y + y⁻¹ = 2 * Real.cos (2 * Real.pi * k / 7) := by
  obtain ⟨k, hk, hyk⟩ := zeta7_isPrimitiveRoot.eq_pow_of_pow_eq_one hy
  exact ⟨k, hk, hyk ▸ zeta7_pow_add_inv k⟩

/-- For each `k`, the discrete plane wave `i ↦ ζ⁷ᵏⁱ` is an eigenvector of the adjacency
matrix of `C₇` with eigenvalue `2 cos (2πk/7)`. -/
lemma huckel_C7_eigenvector (k : ℕ) :
    ∃ v : ZMod 7 → ℂ, v ≠ 0 ∧
      C7adj.mulVec v = (2 * Real.cos (2 * Real.pi * k / 7) : ℂ) • v := by
  set y : ℂ := zeta7 ^ k with hy_def
  have hy7 : y ^ 7 = 1 := by
    rw [hy_def, ← pow_mul, mul_comm, pow_mul, zeta7_pow_seven, one_pow]
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hy7
    simp at hy7
  refine ⟨fun i => y ^ i.val, ?_, ?_⟩
  · intro hcon
    simpa using congrFun hcon 0
  · funext i
    have hval1 : ((1 : ZMod 7)).val = 1 := rfl
    have hnext : y ^ ((i + 1 : ZMod 7)).val = y ^ i.val * y := by
      rw [pow_val_add hy7 i 1, hval1, pow_one]
    have hprev : y ^ ((i - 1 : ZMod 7)).val = y ^ i.val * y⁻¹ := by
      have h2 : y ^ ((i - 1 : ZMod 7) + 1).val = y ^ ((i - 1 : ZMod 7)).val * y := by
        rw [pow_val_add hy7 (i - 1) 1, hval1, pow_one]
      rw [sub_add_cancel] at h2
      rw [h2, mul_inv_cancel_right₀ hy0]
    rw [C7adj_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hnext, hprev, ← zeta7_pow_add_inv k]
    ring

/-- **Hückel theory for the C₇ cycle.**  The eigenvalues of the adjacency matrix of the
cycle graph `C₇` are exactly the numbers `2 cos (2πk/7)`, `k = 0, …, 6`. -/
theorem huckel_C7 :
    {μ : ℂ | ∃ v : ZMod 7 → ℂ, v ≠ 0 ∧ C7adj.mulVec v = μ • v}
      = {μ : ℂ | ∃ k : ℕ, k < 7 ∧ μ = 2 * Real.cos (2 * Real.pi * k / 7)} := by
  ext μ
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, hAv⟩
    have h : ∀ i : ZMod 7, v (i + 1) + v (i - 1) = μ * v i := by
      intro i
      have := congrFun hAv i
      rwa [C7adj_mulVec, Pi.smul_apply, smul_eq_mul] at this
    have hstep : ∀ i : ZMod 7, v (i + 1 + 1) = μ * v (i + 1) - v i := by
      intro i
      have h' := h (i + 1)
      rw [add_sub_cancel_right] at h'
      linear_combination h'
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (μ ^ 2 - 4) (n := 2) (by norm_num)
    set z : ℂ := (μ + s) / 2 with hz_def
    have hz : z * (μ - z) = 1 := by
      rw [hz_def]
      field_simp
      linear_combination -hs
    have hzinv : z⁻¹ = μ - z := inv_eq_of_mul_eq_one_right hz
    have hz' : (μ - z) * z = 1 := by rw [mul_comm]; exact hz
    have hzinv' : (μ - z)⁻¹ = z := inv_eq_of_mul_eq_one_right hz'
    set w : ZMod 7 → ℂ := fun i => v (i + 1) - (μ - z) * v i with hw_def
    by_cases hw : w = 0
    · have hshift : ∀ i : ZMod 7, v (i + 1) = (μ - z) * v i := by
        intro i
        have := congrFun hw i
        rw [hw_def] at this
        simpa using sub_eq_zero.mp this
      obtain ⟨k, hk, hkeq⟩ := sum_inv_eq_two_cos (root_of_shift hv hshift)
      refine ⟨k, hk, ?_⟩
      rw [hzinv'] at hkeq
      linear_combination hkeq
    · have hshift : ∀ i : ZMod 7, w (i + 1) = z * w i := by
        intro i
        rw [hw_def]
        simp only
        rw [hstep i]
        linear_combination (v i) * hz
      obtain ⟨k, hk, hkeq⟩ := sum_inv_eq_two_cos (root_of_shift hw hshift)
      refine ⟨k, hk, ?_⟩
      rw [hzinv] at hkeq
      linear_combination hkeq
  · rintro ⟨k, hk, rfl⟩
    exact huckel_C7_eigenvector k

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

