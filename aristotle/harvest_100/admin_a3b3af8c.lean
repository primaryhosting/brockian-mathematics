import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- A primitive ninth root of unity. -/
noncomputable def zeta9 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)

/-- The additive character `ZMod 9 → ℂ`, `x ↦ ζ₉ ^ x`. -/
noncomputable def ec (x : ZMod 9) : ℂ := zeta9 ^ x.val

/-- The adjacency matrix of the cycle graph `C₉`, with vertices indexed by `ZMod 9`:
two vertices are adjacent exactly when they differ by `±1`. -/
def C9adj : Matrix (ZMod 9) (ZMod 9) ℂ :=
  fun i j => if i - j = 1 ∨ i - j = -1 then 1 else 0

/-- `C9adj` really is the adjacency matrix of Mathlib's cycle graph on `9` vertices. -/
lemma C9adj_eq_adjMatrix : C9adj = (SimpleGraph.cycleGraph 9).adjMatrix ℂ := by
  have key : ∀ i j : ZMod 9, (i - j = 1 ∨ i - j = -1) ↔ (i - j = 1 ∨ j - i = 1) := by
    intro i j
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linear_combination -h)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linear_combination -h)
  funext i j
  simp only [C9adj, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj]
  congr 1
  exact propext (key i j)

lemma zeta9_isPrimitiveRoot : IsPrimitiveRoot zeta9 9 :=
  Complex.isPrimitiveRoot_exp 9 (by norm_num)

lemma zeta9_pow_nine : zeta9 ^ 9 = 1 := zeta9_isPrimitiveRoot.pow_eq_one

lemma zeta9_pow_mod (n : ℕ) : zeta9 ^ (n % 9) = zeta9 ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 9]
  rw [pow_add, pow_mul, zeta9_pow_nine, one_pow, one_mul]

lemma ec_add (x y : ZMod 9) : ec (x + y) = ec x * ec y := by
  simp only [ec, ZMod.val_add, zeta9_pow_mod, pow_add]

lemma ec_zero : ec 0 = 1 := by simp [ec]

lemma ec_ne_one {c : ZMod 9} (hc : c ≠ 0) : ec c ≠ 1 := by
  intro h
  rw [ec, zeta9_isPrimitiveRoot.pow_eq_one_iff_dvd] at h
  have h9 : c.val < 9 := ZMod.val_lt c
  have hv : c.val = 0 := by rcases h with ⟨m, hm⟩; omega
  exact hc ((ZMod.val_eq_zero c).mp hv)

/-- Character sum: `∑_x e(c x) = 0` for `c ≠ 0`. -/
lemma sum_ec_ne_zero {c : ZMod 9} (hc : c ≠ 0) : ∑ x : ZMod 9, ec (c * x) = 0 := by
  have key : ec c * (∑ x : ZMod 9, ec (c * x)) = ∑ x : ZMod 9, ec (c * x) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight (1 : ZMod 9)) (fun x => ec (c * x))]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.coe_addRight, mul_add, mul_one, ec_add, mul_comm]
  have h2 : (ec c - 1) * (∑ x : ZMod 9, ec (c * x)) = 0 := by linear_combination key
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) (ec_ne_one hc)
  · exact h

lemma sum_ec (c : ZMod 9) : ∑ x : ZMod 9, ec (c * x) = if c = 0 then 9 else 0 := by
  by_cases hc : c = 0
  · simp [hc, ec_zero]
  · simp [hc, sum_ec_ne_zero hc]

/-- Fourier inversion on `ZMod 9`. -/
lemma fourier_inversion (v : ZMod 9 → ℂ) (x : ZMod 9) :
    ∑ k : ZMod 9, ec (k * x) * (∑ y : ZMod 9, ec (-(k * y)) * v y) = 9 * v x := by
  have step : ∀ k : ZMod 9, ec (k * x) * (∑ y : ZMod 9, ec (-(k * y)) * v y)
      = ∑ y : ZMod 9, ec ((x - y) * k) * v y := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← mul_assoc, ← ec_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun k _ => step k), Finset.sum_comm]
  have h2 : ∀ y : ZMod 9, ∑ k : ZMod 9, ec ((x - y) * k) * v y
      = (if y = x then (9 : ℂ) else 0) * v y := by
    intro y
    rw [← Finset.sum_mul, sum_ec]
    congr 1
    simp [sub_eq_zero, eq_comm]
  rw [Finset.sum_congr rfl (fun y _ => h2 y)]
  simp

lemma mulVec_apply (v : ZMod 9 → ℂ) (i : ZMod 9) :
    C9adj.mulVec v i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 9) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 9) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have key : ∀ j : ZMod 9, C9adj i j * v j
      = (if j = i - 1 then v j else 0) + (if j = i + 1 then v j else 0) := by
    intro j
    have e1 : (i - j = 1) ↔ j = i - 1 := by
      constructor
      · intro h; linear_combination -h
      · intro h; rw [h]; ring
    have e2 : (i - j = -1) ↔ j = i + 1 := by
      constructor
      · intro h; linear_combination -h
      · intro h; rw [h]; ring
    simp only [C9adj, e1, e2]
    by_cases h1 : j = i - 1
    · simp [h1, hne]
    · by_cases h2 : j = i + 1 <;> simp [h1, h2, hne.symm]
  rw [Matrix.mulVec, dotProduct]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ]
  simp

lemma ec_eq_exp (k : ZMod 9) :
    ec k = Complex.exp (((2 * Real.pi * k.val / 9 : ℝ) : ℂ) * Complex.I) := by
  rw [ec, zeta9, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `e(k) + e(-k) = 2 cos (2πk/9)`. -/
lemma ec_add_ec_neg (k : ZMod 9) :
    ec k + ec (-k) = ((2 * Real.cos (2 * Real.pi * k.val / 9) : ℝ) : ℂ) := by
  have hinv : ec (-k) = (ec k)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← ec_add, neg_add_cancel, ec_zero])
  rw [hinv, ec_eq_exp k, ← Complex.exp_neg,
    show -(((2 * Real.pi * k.val / 9 : ℝ) : ℂ) * Complex.I)
      = (-((2 * Real.pi * k.val / 9 : ℝ) : ℂ)) * Complex.I by ring, ← Complex.two_cos]
  push_cast [Complex.ofReal_cos]
  ring

/-- **Hückel theory for the cycle `C₉`**: a complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₉` if and only if `μ = 2 cos (2πk/9)` for some
`k ∈ {0, 1, …, 8}`. -/
theorem huckel_C9 (μ : ℂ) :
    (∃ v : ZMod 9 → ℂ, v ≠ 0 ∧ C9adj.mulVec v = μ • v) ↔
      ∃ k : ℕ, k < 9 ∧ μ = ((2 * Real.cos (2 * Real.pi * k / 9) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    by_contra hcon
    push_neg at hcon
    apply hv0
    have hmu : ∀ c : ZMod 9, μ ≠ ec c + ec (-c) := by
      intro c h
      have := h.trans (ec_add_ec_neg c)
      exact hcon c.val (ZMod.val_lt c) this
    have happ : ∀ y : ZMod 9, v (y - 1) + v (y + 1) = μ * v y := by
      intro y
      rw [← mulVec_apply v y, hv]
      simp
    have hw : ∀ c : ZMod 9, (∑ y : ZMod 9, ec (-(c * y)) * v y) = 0 := by
      intro c
      set w := ∑ y : ZMod 9, ec (-(c * y)) * v y with hwdef
      have shift1 : ∑ y : ZMod 9, ec (-(c * y)) * v (y - 1) = ec (-c) * w := by
        rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod 9))
          (fun y => ec (-(c * y)) * v (y - 1)), hwdef, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        simp only [Equiv.coe_addRight, add_sub_cancel_right]
        rw [← mul_assoc, ← ec_add]
        congr 2
        ring
      have shift2 : ∑ y : ZMod 9, ec (-(c * y)) * v (y + 1) = ec c * w := by
        rw [← Equiv.sum_comp (Equiv.addRight (-1 : ZMod 9))
          (fun y => ec (-(c * y)) * v (y + 1)), hwdef, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        simp only [Equiv.coe_addRight]
        rw [show y + -1 + 1 = y by ring, ← mul_assoc, ← ec_add]
        congr 2
        ring
      have key : (ec (-c) + ec c) * w = μ * w := by
        have : ∑ y : ZMod 9, ec (-(c * y)) * (v (y - 1) + v (y + 1))
            = ∑ y : ZMod 9, ec (-(c * y)) * (μ * v y) := by
          exact Finset.sum_congr rfl fun y _ => by rw [happ y]
        simp only [mul_add] at this
        rw [Finset.sum_add_distrib, shift1, shift2] at this
        rw [add_mul, this, hwdef, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
      have hzero : (ec (-c) + ec c - μ) * w = 0 := by linear_combination key
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd (by linear_combination -h : μ = ec c + ec (-c)) (hmu c)
      · exact h
    funext x
    have h9 := fourier_inversion v x
    simp only [hw, mul_zero, Finset.sum_const_zero] at h9
    have : (9 : ℂ) ≠ 0 := by norm_num
    simpa using (mul_eq_zero.mp h9.symm).resolve_left this
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun x => ec ((k : ZMod 9) * x), ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp only [mul_zero, ec_zero, Pi.zero_apply] at this
      exact one_ne_zero this
    · funext i
      have hval : ((k : ZMod 9)).val = k := ZMod.val_natCast_of_lt hk
      rw [mulVec_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      have e1 : ec ((k : ZMod 9) * (i - 1)) = ec ((k : ZMod 9) * i) * ec (-(k : ZMod 9)) := by
        rw [← ec_add]; congr 1; ring
      have e2 : ec ((k : ZMod 9) * (i + 1)) = ec ((k : ZMod 9) * i) * ec ((k : ZMod 9)) := by
        rw [← ec_add]; congr 1; ring
      rw [e1, e2, ← mul_add, add_comm (ec (-(k : ZMod 9))) (ec (k : ZMod 9)),
        ec_add_ec_neg (k : ZMod 9), hval]
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

