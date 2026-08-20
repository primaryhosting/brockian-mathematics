/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₇` (the Hückel matrix of a 7-membered
ring, in units where α = 0 and β = 1): the vertices are `Fin 7` and `i` is adjacent to
`i + 1` and `i - 1`, the arithmetic being modulo 7. -/
def C7adj : Matrix (Fin 7) (Fin 7) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

lemma cycleGraph_seven_adj (i j : Fin 7) :
    (SimpleGraph.cycleGraph 7).Adj i j ↔ (j = i + 1 ∨ j = i - 1) := by
  have h := @SimpleGraph.cycleGraph_adj 5 i j
  rw [h]
  clear h
  revert i j
  decide

/-- `C7adj` really is the adjacency matrix of the cycle graph `C₇`. -/
lemma C7adj_eq_adjMatrix : C7adj = (SimpleGraph.cycleGraph 7).adjMatrix ℂ := by
  ext i j
  simp only [C7adj, Matrix.of_apply, SimpleGraph.adjMatrix_apply, cycleGraph_seven_adj]

/-- The basic 7th root of unity `exp (2πi/7)`. -/
noncomputable def w7 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)

lemma isPrimitiveRoot_w7 : IsPrimitiveRoot w7 7 :=
  Complex.isPrimitiveRoot_exp 7 (by norm_num)

lemma w7_pow_seven : w7 ^ 7 = 1 := isPrimitiveRoot_w7.pow_eq_one

lemma w7_ne_zero : w7 ≠ 0 := by
  intro h
  have h7 := w7_pow_seven
  rw [h] at h7
  norm_num at h7

lemma w7_pow_congr {m n : ℕ} (h : m % 7 = n % 7) : w7 ^ m = w7 ^ n := by
  have key : ∀ p : ℕ, w7 ^ p = w7 ^ (p % 7) := by
    intro p
    conv_lhs => rw [← Nat.div_add_mod p 7]
    rw [pow_add, pow_mul, w7_pow_seven, one_pow, one_mul]
  rw [key m, key n, h]

lemma w7_pow_mul (k : ℕ) : w7 ^ k * w7 ^ (6 * k) = 1 := by
  rw [← pow_add]
  have h : k + 6 * k = 7 * k := by ring
  rw [h, pow_mul, w7_pow_seven, one_pow]

lemma w7_pow_inv (k : ℕ) : (w7 ^ k)⁻¹ = w7 ^ (6 * k) :=
  (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact w7_pow_mul k)).symm

lemma w7_pow_eq_exp (k : ℕ) :
    w7 ^ k = Complex.exp (((2 * Real.pi * k / 7 : ℝ) : ℂ) * Complex.I) := by
  rw [w7, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `2 cos(2πk/7)` expressed through the 7th root of unity `w7`. -/
lemma two_cos_eq (k : ℕ) :
    ((2 * Real.cos (2 * Real.pi * k / 7) : ℝ) : ℂ) = w7 ^ k + (w7 ^ k)⁻¹ := by
  rw [w7_pow_eq_exp, ← Complex.exp_neg]
  have hneg : -(((2 * Real.pi * k / 7 : ℝ) : ℂ) * Complex.I)
      = ((-(2 * Real.pi * k / 7) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hneg, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- Action of the adjacency matrix of `C₇` on a vector. -/
lemma C7adj_mulVec (v : Fin 7 → ℂ) (i : Fin 7) :
    (C7adj *ᵥ v) i = v (i + 1) + v (i - 1) := by
  have hn : (-1 : Fin 7) = 6 := by decide
  fin_cases i <;>
    simp [C7adj, Matrix.mulVec, dotProduct, Fin.sum_univ_seven, hn] <;> ring

/-- Going once around the cycle multiplies a geometric function by `c ^ 7`. -/
lemma shift_cycle {c : ℂ} {f : Fin 7 → ℂ} (h : ∀ i : Fin 7, f (i + 1) = c * f i) :
    f 0 = c ^ 7 * f 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  have h5 := h 5; have h6 := h 6
  simp only [Fin.reduceAdd] at h0 h1 h2 h3 h4 h5 h6
  linear_combination h6 + c * h5 + c ^ 2 * h4 + c ^ 3 * h3 + c ^ 4 * h2 + c ^ 5 * h1 + c ^ 6 * h0

/-- A geometric function on the cycle vanishing at `0` vanishes identically. -/
lemma shift_zero_of_zero {c : ℂ} {f : Fin 7 → ℂ} (h : ∀ i : Fin 7, f (i + 1) = c * f i)
    (h0 : f 0 = 0) : ∀ i, f i = 0 := by
  have e0 := h 0; have e1 := h 1; have e2 := h 2; have e3 := h 3; have e4 := h 4
  have e5 := h 5
  simp only [Fin.reduceAdd] at e0 e1 e2 e3 e4 e5
  intro i
  fin_cases i <;> simp_all

/-- **Hückel theory for the cycle `C₇`.**  A complex number `μ` is an eigenvalue of the
adjacency (Hückel) matrix of the 7-cycle if and only if `μ = 2 cos (2πk/7)` for some
`k ∈ {0, …, 6}`. -/
theorem huckel_C7 (μ : ℂ) :
    (∃ v : Fin 7 → ℂ, v ≠ 0 ∧ C7adj *ᵥ v = μ • v) ↔
      ∃ k : Fin 7, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 7) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    have hrec : ∀ i : Fin 7, v (i + 1) + v (i - 1) = μ * v i := by
      intro i
      have hi := congrFun hv i
      rw [C7adj_mulVec] at hi
      simpa using hi
    -- factor `X ^ 2 - μ X + 1 = (X - z) (X - w)` over `ℂ`
    obtain ⟨z, w, hsum, hzw⟩ : ∃ z w : ℂ, z + w = μ ∧ z * w = 1 := by
      obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = μ ^ 2 - 4 :=
        IsAlgClosed.exists_pow_nat_eq _ (by norm_num)
      exact ⟨(μ + s) / 2, (μ - s) / 2, by ring, by field_simp; linear_combination -hs⟩
    obtain ⟨u, hudef⟩ : ∃ u : Fin 7 → ℂ, ∀ i, u i = v (i + 1) - w * v i :=
      ⟨_, fun _ => rfl⟩
    have hu : ∀ i : Fin 7, u (i + 1) = z * u i := by
      intro i
      have h2 : ∀ j : Fin 7, (j + 1 : Fin 7) - 1 = j := by decide
      have h1 := hrec (i + 1)
      rw [h2 i] at h1
      rw [hudef, hudef]
      linear_combination h1 - v (i + 1) * hsum + v i * hzw
    have hz7 : z ^ 7 = 1 := by
      by_cases h0 : u 0 = 0
      · -- then `v` itself is geometric with ratio `w`
        have huz := shift_zero_of_zero hu h0
        have hvrec : ∀ i : Fin 7, v (i + 1) = w * v i := by
          intro i
          have hi := huz i
          rw [hudef] at hi
          linear_combination hi
        have hv00 : v 0 ≠ 0 := fun hc => hv0 (funext (shift_zero_of_zero hvrec hc))
        have hcyc := shift_cycle hvrec
        have hw7 : w ^ 7 = 1 := by
          rcases mul_eq_zero.1 (by linear_combination -hcyc : (w ^ 7 - 1) * v 0 = 0) with h | h
          · linear_combination h
          · exact absurd h hv00
        have hzw7 : (z * w) ^ 7 = 1 := by rw [hzw]; norm_num
        rw [mul_pow, hw7, mul_one] at hzw7
        exact hzw7
      · have hcyc := shift_cycle hu
        rcases mul_eq_zero.1 (by linear_combination -hcyc : (z ^ 7 - 1) * u 0 = 0) with h | h
        · linear_combination h
        · exact absurd h h0
    obtain ⟨i, hi, hzi⟩ := isPrimitiveRoot_w7.eq_pow_of_pow_eq_one hz7
    refine ⟨⟨i, hi⟩, ?_⟩
    have hzne : z ≠ 0 := by
      intro hc
      rw [hc, zero_mul] at hzw
      exact zero_ne_one hzw
    have hwz : w = z⁻¹ := by
      field_simp
      linear_combination hzw
    have hcos := two_cos_eq i
    rw [hzi] at hcos
    push_cast at hcos ⊢
    rw [← hsum, hwz, hcos]
  · rintro ⟨k, rfl⟩
    refine ⟨fun i => w7 ^ ((i : ℕ) * (k : ℕ)), ?_, ?_⟩
    · intro hc
      have h0 := congrFun hc 0
      simp at h0
    · funext i
      rw [C7adj_mulVec]
      have hmu : ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 7) : ℝ) : ℂ)
          = w7 ^ (k : ℕ) + w7 ^ (6 * (k : ℕ)) := by
        rw [two_cos_eq, w7_pow_inv]
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast at hmu ⊢
      rw [hmu, add_mul, ← pow_add, ← pow_add]
      have e2 : ∀ j : Fin 7, (j - 1 : Fin 7) = j + 6 := by decide
      rw [e2 i]
      have ea : ((i + 1 : Fin 7) : ℕ) = ((i : ℕ) + 1) % 7 := Fin.val_add i 1
      have eb : ((i + 6 : Fin 7) : ℕ) = ((i : ℕ) + 6) % 7 := Fin.val_add i 6
      rw [ea, eb]
      have m1 : ((((i : ℕ) + 1) % 7) * (k : ℕ)) % 7
          = ((k : ℕ) + (i : ℕ) * (k : ℕ)) % 7 := by
        conv_lhs => rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
        congr 1
        ring
      have m2 : ((((i : ℕ) + 6) % 7) * (k : ℕ)) % 7
          = (6 * (k : ℕ) + (i : ℕ) * (k : ℕ)) % 7 := by
        conv_lhs => rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
        congr 1
        ring
      rw [w7_pow_congr m1, w7_pow_congr m2]

/-- The same statement, phrased with Mathlib's adjacency matrix of `SimpleGraph.cycleGraph 7`. -/
theorem huckel_C7_adjMatrix (μ : ℂ) :
    (∃ v : Fin 7 → ℂ, v ≠ 0 ∧ (SimpleGraph.cycleGraph 7).adjMatrix ℂ *ᵥ v = μ • v) ↔
      ∃ k : Fin 7, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 7) := by
  rw [← C7adj_eq_adjMatrix]
  exact huckel_C7 μ

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

