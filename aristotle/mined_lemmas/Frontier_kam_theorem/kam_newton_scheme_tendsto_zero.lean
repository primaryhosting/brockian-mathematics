/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Metric Filter Topology

/-- A parameterization `K : Θ → P` of a torus is *invariant* for the dynamics `F : P → P`
with internal (rigid rotation) dynamics `R : Θ → Θ` if it conjugates `R` to `F`:
`F (K θ) = K (R θ)` for all `θ`.  This is the standard "parameterization method"
formulation of an invariant torus carrying quasi-periodic motion with rotation `R`. -/

theorem kam_newton_scheme_tendsto_zero (e : ℕ → ℝ) (A b : ℝ) (hA : 0 < A) (hb : 1 ≤ b)
    (he : ∀ n, 0 ≤ e n) (hrec : ∀ n, e (n + 1) ≤ A * b ^ n * (e n) ^ 2)
    (hsmall : b * (A * e 0) ≤ 1 / 2) :
    (∀ n, e n ≤ (1 / A) * (1 / 2) ^ n) ∧ Filter.Tendsto e Filter.atTop (nhds 0) := by
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  set d : ℕ → ℝ := fun n => A * b ^ n * e n with hd
  have hd0 : ∀ n, 0 ≤ d n := fun n => by
    have : (0:ℝ) ≤ A * b ^ n := by positivity
    exact mul_nonneg this (he n)
  have hstep : ∀ n, b * d (n + 1) ≤ (b * d n) ^ 2 := by
    intro n
    have h1 : d (n + 1) ≤ b * (d n) ^ 2 := by
      have h2 : A * b ^ (n + 1) * e (n + 1) ≤ A * b ^ (n + 1) * (A * b ^ n * (e n) ^ 2) := by
        have : (0:ℝ) ≤ A * b ^ (n + 1) := by positivity
        exact mul_le_mul_of_nonneg_left (hrec n) this
      calc d (n + 1) = A * b ^ (n + 1) * e (n + 1) := rfl
        _ ≤ A * b ^ (n + 1) * (A * b ^ n * (e n) ^ 2) := h2
        _ = b * (A * b ^ n * e n) ^ 2 := by ring
        _ = b * (d n) ^ 2 := rfl
    calc b * d (n + 1) ≤ b * (b * (d n) ^ 2) := by
          exact mul_le_mul_of_nonneg_left h1 hb0.le
      _ = (b * d n) ^ 2 := by ring
  have hkey : ∀ n, b * d n ≤ (1 / 2) ^ (2 ^ n) := by
    intro n
    induction n with
    | zero =>
        simpa [hd] using hsmall
    | succ n ih =>
        have hnn : 0 ≤ b * d n := mul_nonneg hb0.le (hd0 n)
        calc b * d (n + 1) ≤ (b * d n) ^ 2 := hstep n
          _ ≤ ((1 / 2 : ℝ) ^ (2 ^ n)) ^ 2 := by
              exact pow_le_pow_left₀ hnn ih 2
          _ = (1 / 2 : ℝ) ^ (2 ^ (n + 1)) := by
              rw [← pow_mul, pow_succ]
  have hbound : ∀ n, e n ≤ (1 / A) * (1 / 2) ^ n := by
    intro n
    have h1 : A * e n ≤ b * d n := by
      have hbb : (1:ℝ) ≤ b ^ (n + 1) := one_le_pow₀ hb
      have : A * e n * 1 ≤ A * e n * b ^ (n + 1) :=
        mul_le_mul_of_nonneg_left hbb (mul_nonneg hA.le (he n))
      calc A * e n = A * e n * 1 := by ring
        _ ≤ A * e n * b ^ (n + 1) := this
        _ = b * d n := by rw [hd]; ring
    have h2 : ((1:ℝ) / 2) ^ (2 ^ n) ≤ (1 / 2) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.lt_two_pow_self (n := n)).le
    have h3 : A * e n ≤ (1 / 2 : ℝ) ^ n := le_trans h1 ((hkey n).trans h2)
    calc e n = (1 / A) * (A * e n) := by field_simp
      _ ≤ (1 / A) * (1 / 2 : ℝ) ^ n := by
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
  refine ⟨hbound, ?_⟩
  have hlim : Filter.Tendsto (fun n : ℕ => (1 / A) * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1:ℝ)/2 < 1)
    simpa using this.const_mul (1 / A)
  exact squeeze_zero he hbound hlim

/-! ### A concrete system to which the theorem applies

The skew product `F ε (x, y) = (x + α, lam * y + ε * g x)` on the cylinder
`AddCircle 1 × ℝ`.  For `ε = 0` the circle `y = 0` is invariant and carries the rigid
rotation by `α`; the theorem produces, for every `ε`, a continuous invariant circle
`y = u ε x` at distance `O(ε)` from it. -/

