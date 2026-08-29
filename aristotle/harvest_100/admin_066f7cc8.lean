import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset Matrix

/-- A primitive 20-th root of unity. -/
noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 20)

/-- The adjacency matrix of the cycle graph `C₂₀` (Mathlib's `SimpleGraph.cycleGraph 20`),
with vertices indexed by `ZMod 20`: two vertices are adjacent iff they differ by `1` mod `20`. -/
noncomputable def C20 : Matrix (ZMod 20) (ZMod 20) ℂ := (SimpleGraph.cycleGraph 20).adjMatrix ℂ

lemma C20_apply (i j : ZMod 20) : C20 i j = if i - j = 1 ∨ j - i = 1 then 1 else 0 := by
  simp [C20, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj]

/-- The candidate eigenvector for the eigenvalue `2 cos (2πk/20)`. -/
noncomputable def evec (k : ℕ) : ZMod 20 → ℂ := fun j => w ^ (k * j.val)

lemma w_isPrimitiveRoot : IsPrimitiveRoot w 20 := by
  have := Complex.isPrimitiveRoot_exp 20 (by norm_num)
  simpa [w] using this

lemma w_pow_20 : w ^ 20 = 1 := w_isPrimitiveRoot.pow_eq_one

lemma w_ne_zero : w ≠ 0 := by
  intro h
  have h20 := w_pow_20
  rw [h] at h20
  simp at h20

lemma w_pow_mod {a b : ℕ} (h : a % 20 = b % 20) : w ^ a = w ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 20]
  conv_rhs => rw [← Nat.div_add_mod b 20]
  simp [pow_add, pow_mul, w_pow_20, h]

lemma mulVec_C20 (x : ZMod 20 → ℂ) (i : ZMod 20) :
    (C20 *ᵥ x) i = x (i - 1) + x (i + 1) := by
  have hne : (i - 1 : ZMod 20) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 20) = 0 := by linear_combination -h
    revert h2; decide
  have hiff : ∀ j : ZMod 20, (i - j = 1 ∨ j - i = 1) ↔ (j = i - 1 ∨ j = i + 1) := by
    intro j
    constructor
    · rintro (h | h)
      · exact Or.inl (by linear_combination -h)
      · exact Or.inr (by linear_combination h)
    · rintro (h | h)
      · exact Or.inl (by linear_combination -h)
      · exact Or.inr (by linear_combination h)
  have hstep : ∀ j : ZMod 20,
      C20 i j * x j = if j ∈ ({i - 1, i + 1} : Finset (ZMod 20)) then x j else 0 := by
    intro j
    simp only [C20_apply, hiff j, Finset.mem_insert, Finset.mem_singleton, ite_mul, one_mul,
      zero_mul]
  rw [Matrix.mulVec, dotProduct]
  simp only [hstep]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hne]

lemma w_pow_add_cos (k : ℕ) (hk : k ≤ 20) :
    w ^ k + w ^ (20 - k) = ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ) := by
  have h1 : w ^ k = Complex.exp ((2 * Real.pi * k / 20 : ℝ) * Complex.I) := by
    rw [w, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have h2 : w ^ (20 - k) = Complex.exp (-(2 * Real.pi * k / 20 : ℝ) * Complex.I) := by
    rw [pow_sub₀ w w_ne_zero hk, w_pow_20, one_mul, h1, ← Complex.exp_neg]
    ring_nf
  rw [h1, h2, ← Complex.two_cos]
  push_cast
  ring

lemma evec_succ (k : ℕ) (i : ZMod 20) : evec k (i + 1) = w ^ k * evec k i := by
  have hone : (ZMod.val (1 : ZMod 20)) = 1 := by decide
  have hval : (i + 1 : ZMod 20).val = (i.val + 1) % 20 := by
    rw [ZMod.val_add, hone]
  have h2 : w ^ (k * (i + 1 : ZMod 20).val) = w ^ (k * (i.val + 1)) := by
    apply w_pow_mod
    rw [hval, Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod]
    exact dvd_rfl
  simp only [evec, h2, Nat.mul_add, mul_one, pow_add]
  ring

lemma evec_pred (k : ℕ) (hk : k ≤ 20) (i : ZMod 20) :
    evec k (i - 1) = w ^ (20 - k) * evec k i := by
  have h := evec_succ k (i - 1)
  rw [sub_add_cancel] at h
  rw [h, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk, w_pow_20, one_mul]

lemma C20_mulVec_evec (k : ℕ) (hk : k ≤ 20) :
    C20 *ᵥ evec k = ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ) • evec k := by
  funext i
  rw [mulVec_C20, evec_succ, evec_pred k hk, Pi.smul_apply, smul_eq_mul,
    ← w_pow_add_cos k hk]
  ring

lemma evec_ne_zero (k : ℕ) : evec k ≠ 0 := by
  intro h
  have h0 : evec k 0 = 0 := by rw [h]; rfl
  rw [evec] at h0
  simp at h0

lemma geom_sum_w (t : ZMod 20) :
    ∑ m ∈ range 20, w ^ (m * t.val) = if t = 0 then 20 else 0 := by
  by_cases ht : t = 0
  · subst ht
    simp
  · rw [if_neg ht]
    have hz : w ^ t.val ≠ 1 := by
      intro hz
      have hdvd : (20 : ℕ) ∣ t.val := (w_isPrimitiveRoot.pow_eq_one_iff_dvd _).1 hz
      have hlt : t.val < 20 := ZMod.val_lt t
      have hne : t.val ≠ 0 := by
        intro h0
        exact ht ((ZMod.val_eq_zero t).1 h0)
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
      omega
    have : ∑ m ∈ range 20, w ^ (m * t.val) = ∑ m ∈ range 20, (w ^ t.val) ^ m := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← pow_mul, Nat.mul_comm]
    rw [this, geom_sum_eq hz, ← pow_mul, Nat.mul_comm, pow_mul, w_pow_20, one_pow, sub_self,
      zero_div]

/-- If all `20` discrete Fourier coefficients of `x` vanish, then `x = 0`. -/
lemma fourier_eq_zero (x : ZMod 20 → ℂ) (h : ∀ m < 20, ∑ j, evec m j * x j = 0) : x = 0 := by
  funext i
  have key : ∑ m ∈ range 20, w ^ (m * (-i).val) * (∑ j, evec m j * x j) = 20 * x i := by
    have hin : ∀ m ∈ range 20, w ^ (m * (-i).val) * (∑ j, evec m j * x j)
        = ∑ j, w ^ (m * (j - i).val) * x j := by
      intro m _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hval : (j - i : ZMod 20).val = (j.val + (-i).val) % 20 := by
        rw [sub_eq_add_neg, ZMod.val_add]
      have : w ^ (m * (-i).val) * w ^ (m * j.val) = w ^ (m * (j - i).val) := by
        rw [← pow_add]
        apply w_pow_mod
        rw [hval, Nat.mul_mod, Nat.mod_mod_of_dvd _ dvd_rfl, ← Nat.mul_mod]
        congr 1
        ring
      rw [evec, ← mul_assoc, this]
    have hcollapse : ∀ j : ZMod 20, ∑ m ∈ range 20, w ^ (m * (j - i).val) * x j
        = (if j = i then (20 : ℂ) else 0) * x j := by
      intro j
      rw [← Finset.sum_mul, geom_sum_w (j - i)]
      simp [sub_eq_zero]
    calc ∑ m ∈ range 20, w ^ (m * (-i).val) * (∑ j, evec m j * x j)
        = ∑ m ∈ range 20, ∑ j : ZMod 20, w ^ (m * (j - i).val) * x j :=
          Finset.sum_congr rfl hin
      _ = ∑ j : ZMod 20, ∑ m ∈ range 20, w ^ (m * (j - i).val) * x j := Finset.sum_comm
      _ = ∑ j : ZMod 20, (if j = i then (20 : ℂ) else 0) * x j :=
          Finset.sum_congr rfl fun j _ => hcollapse j
      _ = 20 * x i := by simp
  have hzero : ∑ m ∈ range 20, w ^ (m * (-i).val) * (∑ j, evec m j * x j) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [h m (Finset.mem_range.1 hm), mul_zero]
  rw [hzero] at key
  have h20 : (20 : ℂ) ≠ 0 := by norm_num
  simpa using (mul_eq_zero.1 key.symm).resolve_left h20

/-- Each Fourier coefficient of an eigenvector is killed unless the eigenvalue matches. -/
lemma eigen_fourier (x : ZMod 20 → ℂ) (μ : ℂ) (hx : C20 *ᵥ x = μ • x) (m : ℕ) (hm : m ≤ 20) :
    ((2 * Real.cos (2 * Real.pi * m / 20) : ℝ) : ℂ) * (∑ j, evec m j * x j)
      = μ * ∑ j, evec m j * x j := by
  have e1 : ∑ j : ZMod 20, evec m (j + 1) * x j = ∑ j : ZMod 20, evec m j * x (j - 1) :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod 20)) _ _ (fun j => by simp)
  have e2 : ∑ j : ZMod 20, evec m (j - 1) * x j = ∑ j : ZMod 20, evec m j * x (j + 1) :=
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod 20)) _ _ (fun j => by simp)
  have hshift1 : ∑ j : ZMod 20, evec m j * x (j - 1) = w ^ m * ∑ j, evec m j * x j := by
    rw [← e1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [evec_succ, mul_assoc]
  have hshift2 : ∑ j : ZMod 20, evec m j * x (j + 1) = w ^ (20 - m) * ∑ j, evec m j * x j := by
    rw [← e2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [evec_pred m hm, mul_assoc]
  have hmain : ∑ j : ZMod 20, evec m j * (μ * x j)
      = ((2 * Real.cos (2 * Real.pi * m / 20) : ℝ) : ℂ) * ∑ j, evec m j * x j := by
    have : ∀ j : ZMod 20, evec m j * (μ * x j) = evec m j * (x (j - 1) + x (j + 1)) := by
      intro j
      have := congrFun hx j
      rw [mulVec_C20] at this
      rw [this]
      simp [Pi.smul_apply]
    calc ∑ j : ZMod 20, evec m j * (μ * x j)
        = ∑ j : ZMod 20, (evec m j * x (j - 1) + evec m j * x (j + 1)) :=
          Finset.sum_congr rfl fun j _ => by rw [this j, mul_add]
      _ = ((2 * Real.cos (2 * Real.pi * m / 20) : ℝ) : ℂ) * ∑ j, evec m j * x j := by
          rw [Finset.sum_add_distrib, hshift1, hshift2, ← add_mul, w_pow_add_cos m hm]
  rw [← hmain, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Hückel theory for C₂₀.** The eigenvalues of the adjacency matrix of the cycle graph
`C₂₀` are exactly the numbers `2 cos (2πk/20)`, `k = 0, …, 19`. -/
theorem huckel_C20 :
    {μ : ℂ | ∃ x : ZMod 20 → ℂ, x ≠ 0 ∧ C20 *ᵥ x = μ • x} =
      {μ : ℂ | ∃ k : ℕ, k < 20 ∧ μ = ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ)} := by
  ext μ
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx0, hx⟩
    by_contra hcon
    push_neg at hcon
    refine hx0 (fourier_eq_zero x fun m hm => ?_)
    have h := eigen_fourier x μ hx m (le_of_lt hm)
    have hne : ((2 * Real.cos (2 * Real.pi * m / 20) : ℝ) : ℂ) - μ ≠ 0 := by
      intro h0
      exact hcon m hm (by linear_combination -h0)
    have : (((2 * Real.cos (2 * Real.pi * m / 20) : ℝ) : ℂ) - μ) * (∑ j, evec m j * x j) = 0 := by
      linear_combination h
    exact (mul_eq_zero.1 this).resolve_left hne
  · rintro ⟨k, hk, rfl⟩
    exact ⟨evec k, evec_ne_zero k, C20_mulVec_evec k (le_of_lt hk)⟩

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

