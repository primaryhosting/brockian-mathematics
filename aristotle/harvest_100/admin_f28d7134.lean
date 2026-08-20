/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring `/-! ... -/`, so the header
-- above is a plain block comment; it is repeated as the module docstring below.)

import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- The primitive 13-th root of unity `exp(2πi/13)`. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 13)

/-- The character `x ↦ ω^x` of `ZMod 13`. -/
noncomputable def ch : ZMod 13 → ℂ := fun x => om ^ x.val

/-- The adjacency matrix of the cycle graph `C₁₃`, with vertices indexed by `ZMod 13`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`. -/
def C13 : Matrix (ZMod 13) (ZMod 13) ℂ := fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

lemma om_pow_13 : om ^ 13 = 1 := by
  rw [om, ← Complex.exp_nat_mul]
  rw [show ((13 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 13) = 2 * Real.pi * Complex.I by
    push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma om_pow_mod (m : ℕ) : om ^ (m % 13) = om ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 13]
  rw [pow_add, pow_mul, om_pow_13, one_pow, one_mul]

lemma ch_zero : ch 0 = 1 := by simp [ch]

lemma ch_add (x y : ZMod 13) : ch (x + y) = ch x * ch y := by
  simp only [ch, ZMod.val_add, om_pow_mod, pow_add]

lemma ch_ne_zero (x : ZMod 13) : ch x ≠ 0 := by
  have h : om ≠ 0 := Complex.exp_ne_zero _
  simp [ch, h]

lemma ch_neg (x : ZMod 13) : ch (-x) = (ch x)⁻¹ := by
  have h : ch x * ch (-x) = 1 := by rw [← ch_add]; simp [ch_zero]
  exact (inv_eq_of_mul_eq_one_right h).symm

lemma ch_ne_one {x : ZMod 13} (hx : x ≠ 0) : ch x ≠ 1 := by
  intro h
  have hval : x.val ≠ 0 := fun hv => hx ((ZMod.val_eq_zero x).mp hv)
  have hlt : x.val < 13 := ZMod.val_lt x
  have h' : Complex.exp ((x.val : ℂ) * (2 * Real.pi * Complex.I / 13)) = 1 := by
    rw [Complex.exp_nat_mul]; exact h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h'
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp at hn
  have hz : (x.val : ℤ) = 13 * n := by exact_mod_cast hn
  omega

lemma sum_ch_mul (x : ZMod 13) :
    ∑ k : ZMod 13, ch (k * x) = if x = 0 then 13 else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp [ch_zero]
  · rw [if_neg hx]
    have key : ch x * (∑ k : ZMod 13, ch (k * x)) = ∑ k : ZMod 13, ch (k * x) := by
      rw [Finset.mul_sum]
      have hstep : ∀ k : ZMod 13, ch x * ch (k * x) = ch ((k + 1) * x) := by
        intro k
        rw [show (k + 1) * x = k * x + x by ring, ch_add, mul_comm]
      simp_rw [hstep]
      exact Equiv.sum_comp (Equiv.addRight (1 : ZMod 13)) (fun k => ch (k * x))
    have hzero : (ch x - 1) * (∑ k : ZMod 13, ch (k * x)) = 0 := by
      linear_combination key
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd (by linear_combination h : ch x = 1) (ch_ne_one hx)
    · exact h

/-- The Hückel (adjacency) eigenvalues of `C₁₃`. -/
noncomputable def eig (k : ZMod 13) : ℂ := 2 * Real.cos (2 * Real.pi * k.val / 13)

lemma ch_eq_exp (k : ZMod 13) :
    ch k = Complex.exp (((2 * Real.pi * k.val / 13 : ℝ) : ℂ) * Complex.I) := by
  rw [ch, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma ch_add_ch_neg (k : ZMod 13) : ch k + ch (-k) = eig k := by
  rw [ch_neg, ch_eq_exp, ← Complex.exp_neg, eig, Complex.ofReal_cos, Complex.two_cos]
  ring_nf

/-- The matrix whose columns are the eigenvectors (a discrete Fourier transform matrix). -/
noncomputable def P : Matrix (ZMod 13) (ZMod 13) ℂ := fun i k => ch (i * k)

/-- Thirteen times the inverse of `P`. -/
noncomputable def Q : Matrix (ZMod 13) (ZMod 13) ℂ := fun k j => ch (-(k * j))

lemma P_mul_Q : P * Q = (13 : ℂ) • (1 : Matrix (ZMod 13) (ZMod 13) ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  have hstep : ∀ k : ZMod 13, P i k * Q k j = ch (k * (i - j)) := by
    intro k
    simp only [P, Q]
    rw [← ch_add]
    congr 1
    ring
  simp_rw [hstep, sum_ch_mul]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (by simpa [sub_eq_zero] using h)]
    simp [Matrix.one_apply_ne h]

lemma Q_mul_P : Q * P = (13 : ℂ) • (1 : Matrix (ZMod 13) (ZMod 13) ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  have hstep : ∀ k : ZMod 13, Q i k * P k j = ch (k * (j - i)) := by
    intro k
    simp only [P, Q]
    rw [← ch_add]
    congr 1
    ring
  simp_rw [hstep, sum_ch_mul]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (by simpa [sub_eq_zero, eq_comm] using h)]
    simp [Matrix.one_apply_ne h]

lemma C13_mul_P : C13 * P = P * Matrix.diagonal eig := by
  ext i k
  have hne : i + 1 ≠ i - 1 := by
    intro h
    have h2 : (2 : ZMod 13) = 0 := by linear_combination h
    exact absurd h2 (by decide)
  have hstep : ∀ j : ZMod 13, C13 i j * P j k
      = if j ∈ ({i + 1, i - 1} : Finset (ZMod 13)) then P j k else 0 := by
    intro j
    simp only [C13, Finset.mem_insert, Finset.mem_singleton]
    split <;> simp_all
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  simp_rw [hstep]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hne]
  simp only [P]
  rw [show (i + 1) * k = i * k + k by ring, show (i - 1) * k = i * k + (-k) by ring,
    ch_add, ch_add, ← mul_add, ch_add_ch_neg]

lemma P_mulVec_injective {a b : ZMod 13 → ℂ} (hab : P.mulVec a = P.mulVec b) : a = b := by
  have h13 : (13 : ℂ) • a = (13 : ℂ) • b := by
    have h := congrArg (fun v => Q.mulVec v) hab
    simpa [Matrix.mulVec_mulVec, Q_mul_P, Matrix.smul_mulVec, Matrix.one_mulVec] using h
  exact smul_right_injective (ZMod 13 → ℂ) (by norm_num : (13 : ℂ) ≠ 0) h13

/-- **Hückel theory for the cycle `C₁₃`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₃` if and only if `μ = 2 cos(2πk/13)` for some
`k ∈ {0, 1, …, 12}`. -/
theorem huckel_C13 (μ : ℂ) :
    (∃ v : ZMod 13 → ℂ, v ≠ 0 ∧ C13.mulVec v = μ • v) ↔
      ∃ k : ℕ, k < 13 ∧ μ = 2 * Real.cos (2 * Real.pi * k / 13) := by
  constructor
  · rintro ⟨v, hv, hAv⟩
    set w : ZMod 13 → ℂ := (13 : ℂ)⁻¹ • Q.mulVec v with hwdef
    have hPw : P.mulVec w = v := by
      rw [hwdef, Matrix.mulVec_smul, Matrix.mulVec_mulVec, P_mul_Q]
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
      norm_num
    have hw : w ≠ 0 := by
      intro h
      apply hv
      rw [← hPw, h, Matrix.mulVec_zero]
    have hDw : (Matrix.diagonal eig).mulVec w = μ • w := by
      apply P_mulVec_injective
      rw [Matrix.mulVec_mulVec, ← C13_mul_P, ← Matrix.mulVec_mulVec, hPw, hAv,
        Matrix.mulVec_smul, hPw]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
    have hek : eig k = μ := by
      have := congrFun hDw k
      rw [Matrix.mulVec_diagonal] at this
      simpa using mul_right_cancel₀ (by simpa using hk) (this.trans (by simp))
    refine ⟨k.val, ZMod.val_lt k, ?_⟩
    rw [← hek, eig]
  · rintro ⟨k, hk, hμ⟩
    set K : ZMod 13 := (k : ZMod 13) with hK
    have hKval : K.val = k := ZMod.val_natCast_of_lt hk
    have hμ' : μ = eig K := by rw [hμ, eig, hKval]
    refine ⟨fun i => P i K, ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp only [P, zero_mul, ch_zero, Pi.zero_apply] at h0
      exact one_ne_zero h0
    · funext i
      have h1 : (C13.mulVec fun i => P i K) i = (C13 * P) i K := by
        simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
      rw [h1, C13_mul_P, Matrix.mul_diagonal, hμ', Pi.smul_apply, smul_eq_mul, mul_comm]

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

