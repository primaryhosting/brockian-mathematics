/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- `g n = exp (2πi n / 19)`, the basic 19-th root of unity raised to `n`. -/
noncomputable def g (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * n / 19)

lemma g_add (a b : ℕ) : g (a + b) = g a * g b := by
  simp only [g, ← Complex.exp_add]
  push_cast
  ring_nf

lemma g_zero : g 0 = 1 := by simp [g]

lemma g_nineteen : g 19 = 1 := by
  have h : (2 * (Real.pi : ℂ) * Complex.I * (19 : ℕ) / 19) = 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [g, h, Complex.exp_two_pi_mul_I]

lemma g_mul_nineteen (q : ℕ) : g (19 * q) = 1 := by
  induction q with
  | zero => simp [g_zero]
  | succ n ih =>
      have : 19 * (n + 1) = 19 * n + 19 := by ring
      rw [this, g_add, ih, g_nineteen, one_mul]

lemma g_mod (n : ℕ) : g (n % 19) = g n := by
  conv_rhs => rw [← Nat.div_add_mod n 19]
  rw [g_add, g_mul_nineteen, one_mul]

/-- The 19-th root of unity attached to an element of `ZMod 19`. -/
noncomputable def z19 (x : ZMod 19) : ℂ := g x.val

lemma z19_add (x y : ZMod 19) : z19 (x + y) = z19 x * z19 y := by
  simp only [z19, ZMod.val_add, g_mod, g_add]

lemma z19_zero : z19 0 = 1 := by simp [z19, g_zero]

lemma z19_neg_mul (x : ZMod 19) : z19 x * z19 (-x) = 1 := by
  rw [← z19_add]; simp [z19_zero]

lemma z19_ne_zero (x : ZMod 19) : z19 x ≠ 0 := by
  simp [z19, g, Complex.exp_ne_zero]

lemma z19_ne_one {x : ZMod 19} (hx : x ≠ 0) : z19 x ≠ 1 := by
  intro h
  rw [z19, g, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  field_simp at hn
  have hz : ((x.val : ℤ) : ℂ) = ((19 * n : ℤ) : ℂ) := by push_cast; linear_combination hn
  have hzz : (x.val : ℤ) = 19 * n := by exact_mod_cast hz
  have hdvd : (19 : ℤ) ∣ (x.val : ℤ) := ⟨n, hzz⟩
  have h19 : (19 : ℕ) ∣ x.val := by exact_mod_cast hdvd
  have hlt : x.val < 19 := ZMod.val_lt x
  have hne : x.val ≠ 0 := by
    simpa [ZMod.val_eq_zero] using hx
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h19
  omega

lemma z19_sum_ne_zero {c : ZMod 19} (hc : c ≠ 0) : ∑ k : ZMod 19, z19 (c * k) = 0 := by
  set s : ℂ := ∑ k : ZMod 19, z19 (c * k) with hs
  have hstep : s * z19 c = s := by
    have := Equiv.sum_comp (Equiv.addRight (1 : ZMod 19)) (fun k : ZMod 19 => z19 (c * k))
    rw [hs, Finset.sum_mul]
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : c * (k + 1) = c * k + c := by ring
    simp only [Equiv.coe_addRight, this, z19_add]
  have : s * (z19 c - 1) = 0 := by ring_nf; linear_combination hstep
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd (by linear_combination h) (z19_ne_one hc)

lemma z19_sum_eq (c : ZMod 19) :
    ∑ k : ZMod 19, z19 (c * k) = if c = 0 then 19 else 0 := by
  by_cases hc : c = 0
  · simp [hc, z19_zero]
  · simp [hc, z19_sum_ne_zero hc]

lemma z19_add_neg (x : ZMod 19) :
    z19 x + z19 (-x) = 2 * (Real.cos (2 * Real.pi * x.val / 19) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * x.val / 19 with hθ
  have h1 : z19 x = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [z19, g, hθ]
    congr 1
    push_cast
    ring
  have h2 : z19 (-x) = Complex.exp (-(θ : ℂ) * Complex.I) := by
    have hprod := z19_neg_mul x
    have hx : Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-(θ : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      have hzero : (θ : ℂ) * Complex.I + -(θ : ℂ) * Complex.I = 0 := by ring
      rw [hzero, Complex.exp_zero]
    have hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    rw [h1] at hprod
    exact mul_left_cancel₀ hne (hprod.trans hx.symm)
  rw [h1, h2, Complex.ofReal_cos, Complex.cos]
  ring

/-- The adjacency matrix of the cycle graph `C₁₉`, with vertices indexed by `ZMod 19`. -/
def C19 : Matrix (ZMod 19) (ZMod 19) ℂ :=
  fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

lemma C19_mulVec (v : ZMod 19 → ℂ) (i : ZMod 19) :
    C19.mulVec v i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 19) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 19) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have key : ∀ j : ZMod 19, (if i - j = 1 ∨ j - i = 1 then (1 : ℂ) else 0) * v j
      = (if j = i - 1 then v j else 0) + (if j = i + 1 then v j else 0) := by
    intro j
    have h1 : (i - j = 1) ↔ (j = i - 1) := by
      constructor <;> intro h <;> linear_combination -h
    have h2 : (j - i = 1) ↔ (j = i + 1) := by
      constructor <;> intro h <;> linear_combination h
    by_cases hA : j = i - 1
    · have hB : j ≠ i + 1 := by rw [hA]; exact hne
      simp [hA, hne]
    · by_cases hB : j = i + 1
      · simp [hB, Ne.symm hne]
      · simp [h1, h2, hA, hB]
  simp only [Matrix.mulVec, dotProduct, C19]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib]
  simp

/-- For each `x : ZMod 19`, the vector `j ↦ ζ^(jx)` is an eigenvector of the adjacency matrix
of `C₁₉` with eigenvalue `2 cos (2π x /19)`. -/
lemma C19_eigenvector (x : ZMod 19) :
    C19.mulVec (fun j => z19 (j * x))
      = (2 * (Real.cos (2 * Real.pi * x.val / 19) : ℂ)) • (fun j => z19 (j * x)) := by
  funext i
  rw [C19_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  have e1 : (i - 1) * x = i * x + (-x) := by ring
  have e2 : (i + 1) * x = i * x + x := by ring
  rw [e1, e2, z19_add, z19_add, ← z19_add_neg x]
  ring

/-- Every eigenvalue of the adjacency matrix of `C₁₉` is of the form `ζ^k + ζ^(-k)`.
The proof is by discrete Fourier analysis on `ZMod 19`. -/
lemma C19_eigenvalue_form {μ : ℂ} {v : ZMod 19 → ℂ} (hv0 : v ≠ 0)
    (hv : C19.mulVec v = μ • v) : ∃ x : ZMod 19, μ = z19 x + z19 (-x) := by
  have hvi : ∀ i : ZMod 19, v (i - 1) + v (i + 1) = μ * v i := by
    intro i
    have h := congrFun hv i
    rwa [C19_mulVec, Pi.smul_apply, smul_eq_mul] at h
  set w : ZMod 19 → ℂ := fun k => ∑ j : ZMod 19, v j * z19 (-(j * k)) with hw
  have claim1 : ∀ k : ZMod 19, μ * w k = (z19 k + z19 (-k)) * w k := by
    intro k
    have e1 : ∑ j : ZMod 19, v (j - 1) * z19 (-(j * k)) = z19 (-k) * w k := by
      rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod 19))
        (fun j : ZMod 19 => v (j - 1) * z19 (-(j * k)))]
      rw [hw, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
      have hexp : -((j + 1) * k) = -(j * k) + (-k) := by ring
      rw [hexp, z19_add]
      ring
    have e2 : ∑ j : ZMod 19, v (j + 1) * z19 (-(j * k)) = z19 k * w k := by
      rw [← Equiv.sum_comp (Equiv.subRight (1 : ZMod 19))
        (fun j : ZMod 19 => v (j + 1) * z19 (-(j * k)))]
      rw [hw, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Equiv.subRight_apply, sub_add_cancel]
      have hexp : -((j - 1) * k) = -(j * k) + k := by ring
      rw [hexp, z19_add]
      ring
    calc μ * w k = ∑ j : ZMod 19, (μ * v j) * z19 (-(j * k)) := by
            rw [hw, Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j : ZMod 19, (v (j - 1) * z19 (-(j * k)) + v (j + 1) * z19 (-(j * k))) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← hvi j]
            ring
      _ = z19 (-k) * w k + z19 k * w k := by rw [Finset.sum_add_distrib, e1, e2]
      _ = (z19 k + z19 (-k)) * w k := by ring
  have claim2 : ∃ k : ZMod 19, w k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hv0
    funext j
    have inv : ∑ k : ZMod 19, w k * z19 (j * k) = 19 * v j := by
      have hk : ∀ k : ZMod 19, w k * z19 (j * k)
          = ∑ i : ZMod 19, v i * z19 ((j - i) * k) := by
        intro k
        rw [hw, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hexp : (j - i) * k = -(i * k) + j * k := by ring
        rw [hexp, z19_add]
        ring
      rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_comm]
      have hi : ∀ i : ZMod 19, ∑ k : ZMod 19, v i * z19 ((j - i) * k)
          = if i = j then 19 * v i else 0 := by
        intro i
        rw [← Finset.mul_sum, z19_sum_eq]
        by_cases h : i = j
        · simp [h, mul_comm]
        · have hji : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
          simp [hji, h]
      rw [Finset.sum_congr rfl (fun i _ => hi i)]
      simp
    have h0 : (19 : ℂ) * v j = 0 := by
      rw [← inv]
      exact Finset.sum_eq_zero fun k _ => by rw [hcon k]; ring
    have hvj : v j = 0 := by
      have h19 : (19 : ℂ) ≠ 0 := by norm_num
      exact (mul_eq_zero.1 h0).resolve_left h19
    simpa using hvj
  obtain ⟨k, hk⟩ := claim2
  exact ⟨k, mul_right_cancel₀ hk (claim1 k)⟩

/-- **Hückel theory for the cycle `C₁₉`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph on 19 vertices if and only if it is one of the
19 numbers `2 cos (2πk/19)`, `k = 0, …, 18`. -/
theorem huckel_C19 (μ : ℂ) :
    (∃ v : ZMod 19 → ℂ, v ≠ 0 ∧ C19.mulVec v = μ • v) ↔
      ∃ k : ℕ, k < 19 ∧ μ = 2 * (Real.cos (2 * Real.pi * k / 19) : ℂ) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    obtain ⟨x, hx⟩ := C19_eigenvalue_form hv0 hv
    exact ⟨x.val, ZMod.val_lt x, by rw [hx, z19_add_neg]⟩
  · rintro ⟨k, hk, rfl⟩
    have hval : ((k : ZMod 19)).val = k := ZMod.val_natCast_of_lt hk
    refine ⟨fun j => z19 (j * (k : ZMod 19)), ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp [z19_zero] at h0
    · have hev := C19_eigenvector (k : ZMod 19)
      rw [hval] at hev
      exact hev

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

