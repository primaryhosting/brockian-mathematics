/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex

/-- The adjacency matrix of the cycle graph `C₇`, indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `7`. -/
noncomputable def C7adj : Matrix (ZMod 7) (ZMod 7) ℂ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

theorem C7adj_apply (i j : ZMod 7) :
    C7adj i j = (if j = i - 1 then (1 : ℂ) else 0) + (if j = i + 1 then 1 else 0) := by
  have e1 : (i - j = 1) ↔ j = i - 1 :=
    ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
  have e2 : (j - i = 1) ↔ j = i + 1 :=
    ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  have hne : (i - 1 : ZMod 7) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 7) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  simp only [C7adj, Matrix.of_apply, e1, e2]
  by_cases h1 : j = i - 1 <;> by_cases h2 : j = i + 1 <;> simp [h1, h2] at * <;> simp_all

/-- The action of the adjacency matrix on a vector: the neighbours of `i` are `i-1` and `i+1`. -/
theorem C7adj_mulVec (v : ZMod 7 → ℂ) (i : ZMod 7) :
    C7adj.mulVec v i = v (i - 1) + v (i + 1) := by
  simp only [Matrix.mulVec, dotProduct, C7adj_apply, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq' Finset.univ]
  simp

/-! ### The primitive 7-th root of unity -/

/-- The primitive `7`-th root of unity `exp(2πi/7)`. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)

theorem zeta_pow_seven : zeta ^ 7 = 1 := by
  rw [zeta, ← Complex.exp_nat_mul,
    show (7 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 7) = 2 * Real.pi * Complex.I by
      push_cast; ring]
  exact Complex.exp_two_pi_mul_I

theorem zeta_pow_congr {m n : ℕ} (h : m % 7 = n % 7) : zeta ^ m = zeta ^ n := by
  have key : ∀ p : ℕ, zeta ^ p = zeta ^ (p % 7) := by
    intro p
    conv_lhs => rw [show p = 7 * (p / 7) + p % 7 from (Nat.div_add_mod p 7).symm]
    rw [pow_add, pow_mul, zeta_pow_seven, one_pow, one_mul]
  rw [key m, key n, h]

theorem zeta_ne_one : zeta ≠ 1 := by
  intro h
  rw [zeta, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : ((7 * n - 1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
    push_cast
    linear_combination (-7 : ℂ) * hn
  rcases mul_eq_zero.1 h2 with h3 | h3
  · have : (7 * n - 1 : ℤ) = 0 := by exact_mod_cast h3
    omega
  · simp [hpi, Complex.I_ne_zero] at h3

theorem zeta_geom_sum :
    1 + zeta + zeta ^ 2 + zeta ^ 3 + zeta ^ 4 + zeta ^ 5 + zeta ^ 6 = 0 := by
  have hne : zeta - 1 ≠ 0 := sub_ne_zero.mpr zeta_ne_one
  apply mul_left_cancel₀ hne
  rw [mul_zero]
  linear_combination zeta_pow_seven

/-- `2 cos(2πk/7)` expressed via the root of unity. -/
theorem two_cos_eq (k : ℕ) :
    ((2 * Real.cos (2 * Real.pi * k / 7) : ℝ) : ℂ) = zeta ^ k + (zeta ^ k)⁻¹ := by
  have hz : zeta ^ k = Complex.exp (2 * Real.pi * k * Complex.I / 7) := by
    rw [zeta, ← Complex.exp_nat_mul]; ring_nf
  rw [hz, ← Complex.exp_neg]
  push_cast
  have h : Complex.cos (2 * (Real.pi : ℂ) * k / 7)
      = (Complex.exp ((2 * (Real.pi : ℂ) * k / 7) * Complex.I)
        + Complex.exp (-(2 * (Real.pi : ℂ) * k / 7) * Complex.I)) / 2 := by
    rw [Complex.cos]
  rw [h, show (2 * (Real.pi : ℂ) * k / 7) * Complex.I = 2 * Real.pi * k * Complex.I / 7 by ring,
    show (-(2 * (Real.pi : ℂ) * k / 7)) * Complex.I = -(2 * Real.pi * k * Complex.I / 7) by ring]
  ring

/-! ### The eigenvectors -/

/-- The Fourier eigenvector `j ↦ ζ^(k j)`. -/
noncomputable def fourierVec (k : ℕ) : ZMod 7 → ℂ := fun j => zeta ^ (k * j.val)

theorem fourierVec_add (k : ℕ) (a b : ZMod 7) :
    fourierVec k (a + b) = fourierVec k a * fourierVec k b := by
  have h : (a + b).val ≡ a.val + b.val [MOD 7] := by
    rw [ZMod.val_add]; exact Nat.mod_mod _ _
  have h2 : k * (a + b).val ≡ k * a.val + k * b.val [MOD 7] :=
    calc k * (a + b).val ≡ k * (a.val + b.val) [MOD 7] := Nat.ModEq.mul_left k h
      _ = k * a.val + k * b.val := by ring
  rw [fourierVec, fourierVec, fourierVec, ← pow_add]
  exact zeta_pow_congr h2

theorem fourierVec_ne_zero (k : ℕ) : fourierVec k ≠ 0 := by
  intro h
  have h0 : fourierVec k 0 = 0 := by rw [h]; rfl
  rw [fourierVec] at h0
  simp at h0

/-- `ζ^k + ζ^(-k)` is an eigenvalue of the adjacency matrix, with eigenvector `fourierVec k`. -/
theorem C7adj_mulVec_fourierVec (k : ℕ) :
    C7adj.mulVec (fourierVec k) = (zeta ^ k + (zeta ^ k)⁻¹) • fourierVec k := by
  have h7 : (7 : ZMod 7) = 0 := by decide
  have hinv : (zeta ^ k)⁻¹ = zeta ^ (k * 6) := by
    have hmul : zeta ^ k * zeta ^ (k * 6) = 1 := by
      rw [← pow_add, show k + k * 6 = 7 * k by ring, pow_mul, zeta_pow_seven, one_pow]
    exact inv_eq_of_mul_eq_one_right hmul
  funext i
  rw [C7adj_mulVec]
  have hsub : i - 1 = i + 6 := by linear_combination -h7
  rw [hsub, fourierVec_add, fourierVec_add]
  have h1 : fourierVec k 1 = zeta ^ k := by
    rw [fourierVec, show ((1 : ZMod 7)).val = 1 from rfl, mul_one]
  have h6 : fourierVec k 6 = zeta ^ (k * 6) := by
    rw [fourierVec, show ((6 : ZMod 7)).val = 6 from rfl]
  rw [h1, h6, hinv, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The characteristic polynomial identities -/

theorem zeta_inv_one : (zeta ^ 1)⁻¹ = zeta ^ 6 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact zeta_pow_seven)

theorem zeta_inv_two : (zeta ^ 2)⁻¹ = zeta ^ 5 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact zeta_pow_seven)

theorem zeta_inv_three : (zeta ^ 3)⁻¹ = zeta ^ 4 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact zeta_pow_seven)

/-- Elementary symmetric function of degree one of the three nontrivial eigenvalues. -/
theorem esymm_one : (zeta ^ 1 + zeta ^ 6) + (zeta ^ 2 + zeta ^ 5) + (zeta ^ 3 + zeta ^ 4) = -1 := by
  linear_combination zeta_geom_sum

/-- Elementary symmetric function of degree two of the three nontrivial eigenvalues. -/
theorem esymm_two :
    (zeta ^ 1 + zeta ^ 6) * (zeta ^ 2 + zeta ^ 5) + (zeta ^ 1 + zeta ^ 6) * (zeta ^ 3 + zeta ^ 4)
      + (zeta ^ 2 + zeta ^ 5) * (zeta ^ 3 + zeta ^ 4) = -2 := by
  linear_combination (2 * zeta + 2 * zeta ^ 2 + zeta ^ 3 + zeta ^ 4) * zeta_pow_seven
    + 2 * zeta_geom_sum

/-- Elementary symmetric function of degree three of the three nontrivial eigenvalues. -/
theorem esymm_three :
    (zeta ^ 1 + zeta ^ 6) * (zeta ^ 2 + zeta ^ 5) * (zeta ^ 3 + zeta ^ 4) = 1 := by
  linear_combination (zeta ^ 7 + zeta ^ 8 + zeta ^ 5 + zeta ^ 4 + zeta ^ 3 + zeta ^ 2 + zeta + 2)
    * zeta_pow_seven + zeta_geom_sum

/-- The cubic `x³ + x² - 2x - 1` factors over the three nontrivial eigenvalues. -/
theorem cubic_factor (l : ℂ) :
    l ^ 3 + l ^ 2 - 2 * l - 1 =
      (l - (zeta ^ 1 + zeta ^ 6)) * (l - (zeta ^ 2 + zeta ^ 5)) * (l - (zeta ^ 3 + zeta ^ 4)) := by
  linear_combination (l ^ 2 : ℂ) * esymm_one - l * esymm_two + esymm_three

/-! ### Main theorem -/

/-- **Hückel theory for the cycle `C₇`.**  A complex number `l` is an eigenvalue of the
adjacency matrix of the cycle graph `C₇` (i.e. there is a nonzero vector `v` with `A v = l v`)
if and only if `l = 2 cos(2πk/7)` for some `k ∈ {0, 1, …, 6}`. -/
theorem huckel_C7 (l : ℂ) :
    (∃ v : ZMod 7 → ℂ, v ≠ 0 ∧ C7adj.mulVec v = l • v) ↔
      ∃ k : Fin 7, l = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 7) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv, heq⟩
    -- the eigenvalue equation, entrywise
    have key : ∀ j : ZMod 7, v (j - 1) + v (j + 1) = l * v j := by
      intro j
      rw [← C7adj_mulVec, heq, Pi.smul_apply, smul_eq_mul]
    have h0 := key 0
    have h1 := key 1
    have h2 := key 2
    have h3 := key 3
    have h4 := key 4
    have h5 := key 5
    have h6 := key 6
    rw [show (0 : ZMod 7) - 1 = 6 from by decide, show (0 : ZMod 7) + 1 = 1 from by decide] at h0
    rw [show (1 : ZMod 7) - 1 = 0 from by decide, show (1 : ZMod 7) + 1 = 2 from by decide] at h1
    rw [show (2 : ZMod 7) - 1 = 1 from by decide, show (2 : ZMod 7) + 1 = 3 from by decide] at h2
    rw [show (3 : ZMod 7) - 1 = 2 from by decide, show (3 : ZMod 7) + 1 = 4 from by decide] at h3
    rw [show (4 : ZMod 7) - 1 = 3 from by decide, show (4 : ZMod 7) + 1 = 5 from by decide] at h4
    rw [show (5 : ZMod 7) - 1 = 4 from by decide, show (5 : ZMod 7) + 1 = 6 from by decide] at h5
    rw [show (6 : ZMod 7) - 1 = 5 from by decide, show (6 : ZMod 7) + 1 = 0 from by decide] at h6
    -- solve the recurrence in terms of `v 0` and `v 1`
    have e2 : v 2 = l * v 1 - v 0 := by linear_combination h1
    have e3 : v 3 = (l ^ 2 - 1) * v 1 - l * v 0 := by linear_combination h2 + l * e2
    have e4 : v 4 = (l ^ 3 - 2 * l) * v 1 - (l ^ 2 - 1) * v 0 := by
      linear_combination h3 + l * e3 - e2
    have e5 : v 5 = (l ^ 4 - 3 * l ^ 2 + 1) * v 1 - (l ^ 3 - 2 * l) * v 0 := by
      linear_combination h4 + l * e4 - e3
    have e6 : v 6 = (l ^ 5 - 4 * l ^ 3 + 3 * l) * v 1 - (l ^ 4 - 3 * l ^ 2 + 1) * v 0 := by
      linear_combination h5 + l * e5 - e4
    -- the two closing equations
    have E1 : (l ^ 6 - 5 * l ^ 4 + 6 * l ^ 2 - 1) * v 1 = (l ^ 5 - 4 * l ^ 3 + 3 * l + 1) * v 0 := by
      linear_combination (-1 : ℂ) * h6 + e5 - l * e6
    have E2 : (l ^ 5 - 4 * l ^ 3 + 3 * l + 1) * v 1 = (l ^ 4 - 3 * l ^ 2 + l + 1) * v 0 := by
      linear_combination h0 - e6
    -- eliminate
    have P0 : (l ^ 7 - 7 * l ^ 5 + 14 * l ^ 3 - 7 * l - 2) * v 0 = 0 := by
      linear_combination (l ^ 5 - 4 * l ^ 3 + 3 * l + 1) * E1
        - (l ^ 6 - 5 * l ^ 4 + 6 * l ^ 2 - 1) * E2
    have P1 : (l ^ 7 - 7 * l ^ 5 + 14 * l ^ 3 - 7 * l - 2) * v 1 = 0 := by
      linear_combination (l ^ 4 - 3 * l ^ 2 + l + 1) * E1
        - (l ^ 5 - 4 * l ^ 3 + 3 * l + 1) * E2
    have hp : l ^ 7 - 7 * l ^ 5 + 14 * l ^ 3 - 7 * l - 2 = 0 := by
      by_contra hne
      apply hv
      have hv0 : v 0 = 0 := by
        rcases mul_eq_zero.1 P0 with h | h
        · exact absurd h hne
        · exact h
      have hv1 : v 1 = 0 := by
        rcases mul_eq_zero.1 P1 with h | h
        · exact absurd h hne
        · exact h
      have hv2 : v 2 = 0 := by rw [e2, hv0, hv1]; ring
      have hv3 : v 3 = 0 := by rw [e3, hv0, hv1]; ring
      have hv4 : v 4 = 0 := by rw [e4, hv0, hv1]; ring
      have hv5 : v 5 = 0 := by rw [e5, hv0, hv1]; ring
      have hv6 : v 6 = 0 := by rw [e6, hv0, hv1]; ring
      funext j
      fin_cases j <;> assumption
    -- factor the characteristic polynomial
    have hfac : (l - 2) * (l ^ 3 + l ^ 2 - 2 * l - 1) ^ 2 = 0 := by linear_combination hp
    rcases mul_eq_zero.1 hfac with h | h
    · refine ⟨0, ?_⟩
      have hl : l = 2 := by linear_combination h
      rw [hl]
      norm_num
    · have hq : l ^ 3 + l ^ 2 - 2 * l - 1 = 0 := by
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      rw [cubic_factor] at hq
      rcases mul_eq_zero.1 hq with h' | h'
      · rcases mul_eq_zero.1 h' with h'' | h''
        · refine ⟨1, ?_⟩
          rw [show ((1 : Fin 7) : ℕ) = 1 from rfl, two_cos_eq 1, zeta_inv_one]
          linear_combination h''
        · refine ⟨2, ?_⟩
          rw [show ((2 : Fin 7) : ℕ) = 2 from rfl, two_cos_eq 2, zeta_inv_two]
          linear_combination h''
      · refine ⟨3, ?_⟩
        rw [show ((3 : Fin 7) : ℕ) = 3 from rfl, two_cos_eq 3, zeta_inv_three]
        linear_combination h'
  · rintro ⟨k, rfl⟩
    refine ⟨fourierVec (k : ℕ), fourierVec_ne_zero _, ?_⟩
    rw [C7adj_mulVec_fourierVec, two_cos_eq]

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

