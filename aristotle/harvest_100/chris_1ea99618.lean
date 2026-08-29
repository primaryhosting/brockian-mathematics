import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₀`, with vertices indexed by `ZMod 10`:
`i` and `j` are adjacent iff they differ by `1` modulo `10`. -/
def cycleAdj10 : Matrix (ZMod 10) (ZMod 10) ℝ :=
  fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- A primitive `10`-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

/-- The additive character `m ↦ ζ ^ m` on `ZMod 10`. -/
noncomputable def ee (m : ZMod 10) : ℂ := zeta ^ m.val

lemma zeta_prim : IsPrimitiveRoot zeta 10 := by
  simpa [zeta] using Complex.isPrimitiveRoot_exp 10 (by norm_num)

lemma zeta_pow_ten : zeta ^ 10 = 1 := zeta_prim.pow_eq_one

lemma zeta_pow_mod (n : ℕ) : zeta ^ (n % 10) = zeta ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 10]
  rw [pow_add, pow_mul, zeta_pow_ten, one_pow, one_mul]

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_add (a b : ZMod 10) : ee (a + b) = ee a * ee b := by
  simp only [ee, ZMod.val_add, zeta_pow_mod, pow_add]

lemma ee_mul (m k : ZMod 10) : ee (m * k) = ee m ^ k.val := by
  simp only [ee, ZMod.val_mul, zeta_pow_mod, pow_mul]

lemma ee_ne_one {m : ZMod 10} (hm : m ≠ 0) : ee m ≠ 1 := by
  intro h
  apply hm
  have hlt : m.val < 10 := ZMod.val_lt m
  have hdvd := (zeta_prim.pow_eq_one_iff_dvd m.val).1 h
  have hz : m.val = 0 := by
    rcases Nat.eq_zero_or_pos m.val with h0 | h0
    · exact h0
    · exact absurd (Nat.le_of_dvd h0 hdvd) (by omega)
  exact (ZMod.val_eq_zero m).1 hz

lemma ee_pow_ten (m : ZMod 10) : ee m ^ 10 = 1 := by
  rw [ee, ← pow_mul, mul_comm, pow_mul, zeta_pow_ten, one_pow]

/-- Orthogonality relation for the characters of `ZMod 10`. -/
lemma sum_ee (m : ZMod 10) : ∑ k : ZMod 10, ee (m * k) = if m = 0 then 10 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [ee_zero]
  · simp only [hm, if_false]
    have h0 : (∑ k : ZMod 10, ee (m * k)) = ∑ j ∈ Finset.range 10, ee m ^ j := by
      rw [show (∑ k : ZMod 10, ee (m * k)) = ∑ j ∈ Finset.range 10, ee (m * (j : ZMod 10)) from rfl]
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp only [Finset.mem_range] at hj
      rw [ee_mul, ZMod.val_natCast_of_lt hj]
    rw [h0, geom_sum_eq (ee_ne_one hm), ee_pow_ten, sub_self, zero_div]

lemma adj_sum {R : Type*} [CommRing R] (f : ZMod 10 → R) (i : ZMod 10) :
    ∑ j : ZMod 10, (if i - j = 1 ∨ j - i = 1 then (1 : R) else 0) * f j
      = f (i - 1) + f (i + 1) := by
  have hne : ∀ a : ZMod 10, a - 1 ≠ a + 1 := by decide
  have hiff : ∀ a b : ZMod 10, (a - b = 1 ∨ b - a = 1) ↔ (b = a - 1 ∨ b = a + 1) := by decide
  have key : ∀ j : ZMod 10,
      (if i - j = 1 ∨ j - i = 1 then (1 : R) else 0) * f j
        = (if j = i - 1 then f j else 0) + (if j = i + 1 then f j else 0) := by
    intro j
    rw [if_congr (hiff i j) rfl rfl]
    by_cases h1 : j = i - 1
    · subst h1
      simp [hne i]
    · by_cases h2 : j = i + 1
      · subst h2
        simp [h1]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib]
  simp

lemma ee_eq_exp (m : ZMod 10) :
    ee m = Complex.exp (((2 * Real.pi * m.val / 10 : ℝ) : ℂ) * Complex.I) := by
  rw [ee, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma ee_add_ee_neg (m : ZMod 10) :
    ee m + ee (-m) = ((2 * Real.cos (2 * Real.pi * m.val / 10) : ℝ) : ℂ) := by
  set t : ℝ := 2 * Real.pi * m.val / 10 with ht
  have h1 : ee m = Complex.exp ((t : ℂ) * Complex.I) := ee_eq_exp m
  have hmul : ee m * ee (-m) = 1 := by rw [← ee_add]; simp [ee_zero]
  have hne : ee m ≠ 0 := by rw [h1]; exact Complex.exp_ne_zero _
  have h2 : ee (-m) = Complex.exp (-((t : ℂ) * Complex.I)) := by
    rw [Complex.exp_neg, ← h1]
    exact Eq.symm (DivisionMonoid.inv_eq_of_mul (ee m) (ee (-m)) hmul)
  rw [h1, h2, Complex.exp_mul_I, neg_mul_eq_neg_mul, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

lemma cycleAdj10_mulVec (v : ZMod 10 → ℝ) (i : ZMod 10) :
    cycleAdj10.mulVec v i = v (i - 1) + v (i + 1) := by
  have h : cycleAdj10.mulVec v i
      = ∑ j : ZMod 10, (if i - j = 1 ∨ j - i = 1 then (1 : ℝ) else 0) * v j := rfl
  rw [h, adj_sum]

/-- The discrete Fourier transform is injective on `ZMod 10`-indexed vectors. -/
lemma dft_inj (V : ZMod 10 → ℂ) (h : ∀ k : ZMod 10, (∑ j : ZMod 10, V j * ee (j * k)) = 0) :
    V = 0 := by
  funext j0
  have key : (0 : ℂ) = ∑ j : ZMod 10, V j * (if j - j0 = 0 then (10 : ℂ) else 0) := by
    calc (0 : ℂ) = ∑ k : ZMod 10, (∑ j : ZMod 10, V j * ee (j * k)) * ee (-(j0 * k)) := by
          simp [h]
      _ = ∑ k : ZMod 10, ∑ j : ZMod 10, V j * ee ((j - j0) * k) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [mul_assoc, ← ee_add]
          congr 2
          ring
      _ = ∑ j : ZMod 10, ∑ k : ZMod 10, V j * ee ((j - j0) * k) := Finset.sum_comm
      _ = ∑ j : ZMod 10, V j * (if j - j0 = 0 then (10 : ℂ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [← Finset.mul_sum, sum_ee]
  simp only [sub_eq_zero, mul_ite, mul_zero, Finset.sum_ite_eq' Finset.univ j0] at key
  simp at key
  simpa using key

/-- The Fourier coefficients of an eigenvector diagonalize the cyclic recurrence. -/
lemma dft_eigen (V : ZMod 10 → ℂ) (c : ℂ)
    (hrec : ∀ i : ZMod 10, V (i - 1) + V (i + 1) = c * V i) (k : ZMod 10) :
    (ee k + ee (-k)) * (∑ j : ZMod 10, V j * ee (j * k))
      = c * (∑ j : ZMod 10, V j * ee (j * k)) := by
  have hS1 : ∑ j : ZMod 10, V (j - 1) * ee (j * k) = ee k * ∑ j : ZMod 10, V j * ee (j * k) := by
    rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod 10)) (fun j : ZMod 10 => V (j - 1) * ee (j * k))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [show (j + 1) * k = j * k + k by ring, ee_add]
    ring
  have hS2 : ∑ j : ZMod 10, V (j + 1) * ee (j * k)
      = ee (-k) * ∑ j : ZMod 10, V j * ee (j * k) := by
    rw [← Equiv.sum_comp (Equiv.addRight (-1 : ZMod 10))
      (fun j : ZMod 10 => V (j + 1) * ee (j * k))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp only [Equiv.coe_addRight]
    rw [show j + -1 + 1 = j by ring, show (j + -1) * k = j * k + -k by ring, ee_add]
    ring
  calc (ee k + ee (-k)) * (∑ j : ZMod 10, V j * ee (j * k))
      = (∑ j : ZMod 10, V (j - 1) * ee (j * k)) + ∑ j : ZMod 10, V (j + 1) * ee (j * k) := by
        rw [hS1, hS2, add_mul]
    _ = ∑ j : ZMod 10, (V (j - 1) + V (j + 1)) * ee (j * k) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = c * (∑ j : ZMod 10, V j * ee (j * k)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [hrec j]; ring

/-- **Hückel theory for the C₁₀ cycle.**  A real number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₁₀` if and only if `μ = 2 cos (2πk/10)` for some `k ∈ {0, …, 9}`. -/
theorem huckel_C10 (μ : ℝ) :
    (∃ v : ZMod 10 → ℝ, v ≠ 0 ∧ cycleAdj10.mulVec v = μ • v) ↔
      ∃ k : ℕ, k < 10 ∧ μ = 2 * Real.cos (2 * Real.pi * k / 10) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    have hrec : ∀ i : ZMod 10, ((v (i - 1) : ℂ)) + (v (i + 1) : ℂ) = (μ : ℂ) * (v i : ℂ) := by
      intro i
      have h := congrFun hv i
      rw [cycleAdj10_mulVec] at h
      simp only [Pi.smul_apply, smul_eq_mul] at h
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
    have hex : ∃ k : ZMod 10, (∑ j : ZMod 10, (v j : ℂ) * ee (j * k)) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have := dft_inj (fun j => (v j : ℂ)) hcon
      apply hv0
      funext j
      have := congrFun this j
      simpa using this
    obtain ⟨k, hk⟩ := hex
    refine ⟨k.val, ZMod.val_lt k, ?_⟩
    have hc : ee k + ee (-k) = (μ : ℂ) :=
      mul_right_cancel₀ hk (dft_eigen (fun j => (v j : ℂ)) (μ : ℂ) hrec k)
    rw [ee_add_ee_neg] at hc
    exact_mod_cast hc.symm
  · rintro ⟨k, hk10, hmu⟩
    have hval : ((k : ZMod 10)).val = k := ZMod.val_natCast_of_lt hk10
    refine ⟨fun j => (ee ((k : ZMod 10) * j)).re, ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp [ee_zero] at h0
    · funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [cycleAdj10_mulVec]
      have h1 : ee ((k : ZMod 10) * (i - 1)) = ee (-(k : ZMod 10)) * ee ((k : ZMod 10) * i) := by
        rw [← ee_add]; congr 1; ring
      have h2 : ee ((k : ZMod 10) * (i + 1)) = ee ((k : ZMod 10)) * ee ((k : ZMod 10) * i) := by
        rw [← ee_add]; congr 1; ring
      have h3 : ee (-(k : ZMod 10)) + ee ((k : ZMod 10)) = ((μ : ℝ) : ℂ) := by
        rw [add_comm, ee_add_ee_neg, hval, hmu]
      have h4 : (ee ((k : ZMod 10) * (i - 1))).re + (ee ((k : ZMod 10) * (i + 1))).re
          = (((μ : ℝ) : ℂ) * ee ((k : ZMod 10) * i)).re := by
        rw [h1, h2, ← Complex.add_re, ← add_mul, h3]
      rw [h4, Complex.re_ofReal_mul]

end Chem

