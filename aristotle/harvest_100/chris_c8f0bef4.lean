/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not
-- permit a module docstring before the `import` line.)

import Mathlib

namespace Chem

open Finset Complex Matrix

/-- A primitive 16-th root of unity. -/
noncomputable def zeta16 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

lemma zeta16_primitive : IsPrimitiveRoot zeta16 16 := by
  have h := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  simpa [zeta16] using h

lemma zeta16_pow16 : zeta16 ^ 16 = 1 := zeta16_primitive.pow_eq_one

lemma zeta16_pow_mod (a : ℕ) : zeta16 ^ (a % 16) = zeta16 ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 16]
  rw [pow_add, pow_mul, zeta16_pow16, one_pow, one_mul]

/-- The standard additive character of `ZMod 16`, `x ↦ ζ ^ x`. -/
noncomputable def ch (x : ZMod 16) : ℂ := zeta16 ^ x.val

lemma ch_add (x y : ZMod 16) : ch (x + y) = ch x * ch y := by
  simp only [ch, ZMod.val_add, zeta16_pow_mod, pow_add]

lemma ch_zero : ch 0 = 1 := by simp [ch]

lemma ch_ne_zero (x : ZMod 16) : ch x ≠ 0 := by
  simp only [ch]
  exact pow_ne_zero _ (by simp [zeta16, Complex.exp_ne_zero])

lemma ch_nsmul (n : ℕ) (x : ZMod 16) : ch (n • x) = ch x ^ n := by
  induction n with
  | zero => simpa using ch_zero
  | succ n ih => rw [succ_nsmul, ch_add, ih, pow_succ]

lemma ch_mul (k m : ZMod 16) : ch (k * m) = ch m ^ k.val := by
  rw [← ch_nsmul]
  congr 1
  rw [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]

lemma ch_pow16 (m : ZMod 16) : ch m ^ 16 = 1 := by
  rw [ch, ← pow_mul, mul_comm, pow_mul, zeta16_pow16, one_pow]

lemma ch_ne_one {m : ZMod 16} (hm : m ≠ 0) : ch m ≠ 1 := by
  intro h
  have hdvd : (16 : ℕ) ∣ m.val := (zeta16_primitive.pow_eq_one_iff_dvd m.val).1 h
  have hlt : m.val < 16 := m.val_lt
  have hpos : m.val ≠ 0 := fun h0 => hm ((ZMod.val_eq_zero m).1 h0)
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hdvd) (by omega)

/-- Orthogonality of characters on `ZMod 16`. -/
lemma ch_sum (m : ZMod 16) : ∑ k : ZMod 16, ch (k * m) = if m = 0 then 16 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [ch_zero]
  · simp only [hm, if_false]
    have hre : ∑ k : ZMod 16, ch m ^ (ZMod.val k) = ∑ i ∈ Finset.range 16, ch m ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => ch m ^ i) 16
    have : ∑ k : ZMod 16, ch (k * m) = ∑ i ∈ Finset.range 16, ch m ^ i := by
      rw [← hre]
      exact Finset.sum_congr rfl fun k _ => ch_mul k m
    rw [this, geom_sum_eq (ch_ne_one hm), ch_pow16, sub_self, zero_div]

/-- The adjacency matrix of the cycle graph `C₁₆`, with vertices indexed by `ZMod 16`:
two vertices are adjacent exactly when they differ by `1`. -/
def C16 : Matrix (ZMod 16) (ZMod 16) ℂ := fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

lemma C16_mulVec (v : ZMod 16 → ℂ) (i : ZMod 16) :
    (C16 *ᵥ v) i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 16) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 16) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have key : ∀ j : ZMod 16,
      C16 i j * v j = (if j = i - 1 then v j else 0) + (if j = i + 1 then v j else 0) := by
    intro j
    by_cases h1 : j = i - 1
    · subst h1
      have : (i - (i - 1) : ZMod 16) = 1 := by ring
      simp [C16, this, hne]
    · by_cases h2 : j = i + 1
      · subst h2
        have : (i + 1 - i : ZMod 16) = 1 := by ring
        have h3 : (i - (i + 1) : ZMod 16) ≠ 1 := by
          intro h
          have : (2 : ZMod 16) = 0 := by linear_combination -h
          exact absurd this (by decide)
        simp [C16, this, h1]
      · have e1 : ¬ (i - j = 1) := by
          intro h; exact h1 (by linear_combination -h)
        have e2 : ¬ (j - i = 1) := by
          intro h; exact h2 (by linear_combination h)
        simp [C16, e1, e2, h1, h2]
  simp only [Matrix.mulVec, dotProduct, key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i - 1) v,
    Finset.sum_ite_eq' Finset.univ (i + 1) v]
  simp only [Finset.mem_univ, if_true]

/-- The character vector `j ↦ ch (k * j)` is an eigenvector of the adjacency matrix. -/
lemma C16_mulVec_ch (k : ZMod 16) :
    C16 *ᵥ (fun j => ch (k * j)) = (ch k + ch (-k)) • (fun j => ch (k * j)) := by
  funext i
  rw [C16_mulVec]
  have h1 : k * (i - 1) = k * i + (-k) := by ring
  have h2 : k * (i + 1) = k * i + k := by ring
  simp only [h1, h2, ch_add, Pi.smul_apply, smul_eq_mul]
  ring

lemma ch_eq_exp (k : ZMod 16) :
    ch k = Complex.exp ((2 * Real.pi * (k.val : ℝ) / 16 : ℝ) * Complex.I) := by
  rw [ch, zeta16, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The eigenvalue attached to the character indexed by `k`. -/
lemma ch_add_ch_neg (k : ZMod 16) :
    ch k + ch (-k) = 2 * (Real.cos (2 * Real.pi * (k.val : ℝ) / 16) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * (k.val : ℝ) / 16 with hθ
  have hprod : ch k * ch (-k) = 1 := by rw [← ch_add]; simp [ch_zero]
  have hk : ch k = Complex.exp ((θ : ℂ) * Complex.I) := ch_eq_exp k
  have hnk : ch (-k) = Complex.exp (-((θ : ℂ) * Complex.I)) := by
    have hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have : Complex.exp ((θ : ℂ) * Complex.I) * ch (-k)
        = Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-((θ : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, ← hk, hprod]
    exact mul_left_cancel₀ hne this
  rw [hk, hnk, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-- **Hückel theory for the C₁₆ annulene ring.**
The eigenvalues of the adjacency matrix of the cycle graph `C₁₆` are exactly the
sixteen numbers `2 cos (2πk/16)`, `k = 0, …, 15`. -/
theorem huckel_C16 (μ : ℂ) :
    (∃ v : ZMod 16 → ℂ, v ≠ 0 ∧ C16 *ᵥ v = μ • v) ↔
      ∃ k : Fin 16, μ = 2 * (Real.cos (2 * Real.pi * (k : ℕ) / 16) : ℂ) := by
  constructor
  · rintro ⟨v, hv, hAv⟩
    by_contra hcon
    push_neg at hcon
    -- Fourier coefficients of `v`
    set c : ZMod 16 → ℂ := fun k => ∑ j : ZMod 16, ch (-(k * j)) * v j with hc
    have hshift : ∀ k : ZMod 16, ∑ j : ZMod 16, ch (-(k * j)) * v (j - 1) = ch (-k) * c k := by
      intro k
      have := Fintype.sum_equiv (Equiv.addRight (1 : ZMod 16))
        (fun j : ZMod 16 => ch (-(k * (j + 1))) * v j)
        (fun j : ZMod 16 => ch (-(k * j)) * v (j - 1)) (fun j => by simp)
      rw [← this, hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show ch (-(k * (j + 1))) * v j = ch (-k) * (ch (-(k * j)) * v j)
      have h : -(k * (j + 1)) = -k + -(k * j) := by ring
      rw [h, ch_add]
      ring
    have hshift' : ∀ k : ZMod 16, ∑ j : ZMod 16, ch (-(k * j)) * v (j + 1) = ch k * c k := by
      intro k
      have := Fintype.sum_equiv (Equiv.addRight (-1 : ZMod 16))
        (fun j : ZMod 16 => ch (-(k * (j - 1))) * v j)
        (fun j : ZMod 16 => ch (-(k * j)) * v (j + 1)) (fun j => by simp [sub_eq_add_neg])
      rw [← this, hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show ch (-(k * (j - 1))) * v j = ch k * (ch (-(k * j)) * v j)
      have h : -(k * (j - 1)) = k + -(k * j) := by ring
      rw [h, ch_add]
      ring
    have hkey : ∀ k : ZMod 16, (ch k + ch (-k)) * c k = μ * c k := by
      intro k
      have h1 : ∑ j : ZMod 16, ch (-(k * j)) * ((C16 *ᵥ v) j) = (ch k + ch (-k)) * c k := by
        have : ∀ j : ZMod 16, ch (-(k * j)) * ((C16 *ᵥ v) j)
            = ch (-(k * j)) * v (j - 1) + ch (-(k * j)) * v (j + 1) := by
          intro j; rw [C16_mulVec]; ring
        rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, hshift, hshift']
        ring
      have h2 : ∑ j : ZMod 16, ch (-(k * j)) * ((C16 *ᵥ v) j) = μ * c k := by
        rw [hAv, hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [← h1, h2]
    have hczero : ∀ k : ZMod 16, c k = 0 := by
      intro k
      have hne : ch k + ch (-k) ≠ μ := by
        rw [ch_add_ch_neg k]
        intro h
        exact hcon (⟨k.val, k.val_lt⟩ : Fin 16) (by simpa using h.symm)
      have := hkey k
      have : (ch k + ch (-k) - μ) * c k = 0 := by linear_combination this
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) hne
      · exact h
    apply hv
    funext j
    have hinv : ∑ k : ZMod 16, ch (k * j) * c k = 16 * v j := by
      have step : ∀ k : ZMod 16, ch (k * j) * c k
          = ∑ l : ZMod 16, ch (k * (j - l)) * v l := by
        intro k
        rw [hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        have : k * (j - l) = k * j + -(k * l) := by ring
        rw [this, ch_add]
        ring
      rw [Finset.sum_congr rfl fun k _ => step k, Finset.sum_comm]
      have : ∀ l : ZMod 16, ∑ k : ZMod 16, ch (k * (j - l)) * v l
          = (if j - l = 0 then (16 : ℂ) else 0) * v l := by
        intro l
        rw [← Finset.sum_mul, ch_sum]
      rw [Finset.sum_congr rfl fun l _ => this l]
      have : ∀ l : ZMod 16, (if j - l = 0 then (16 : ℂ) else 0) * v l
          = if l = j then (16 : ℂ) * v l else 0 := by
        intro l
        by_cases h : l = j
        · subst h; simp
        · have : j - l ≠ 0 := fun h0 => h (by linear_combination -h0)
          simp [this, h]
      rw [Finset.sum_congr rfl fun l _ => this l,
        Finset.sum_ite_eq' Finset.univ j (fun l => (16 : ℂ) * v l)]
      simp
    simp only [hczero, mul_zero, Finset.sum_const_zero] at hinv
    have : (16 : ℂ) ≠ 0 := by norm_num
    simpa using (mul_eq_zero.1 hinv.symm).resolve_left this
  · rintro ⟨k, rfl⟩
    refine ⟨fun j => ch (((k : ℕ) : ZMod 16) * j), ?_, ?_⟩
    · intro h
      have h0 : ch (((k : ℕ) : ZMod 16) * 0) = 0 := congrFun h 0
      rw [mul_zero] at h0
      exact ch_ne_zero 0 h0
    · rw [C16_mulVec_ch]
      congr 1
      rw [ch_add_ch_neg]
      congr 2
      rw [ZMod.val_natCast_of_lt k.isLt]

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

