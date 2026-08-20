/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open Filter Metric

/-!
## The zeta datum of a variety over a finite field

Mathlib has no étale cohomology, so we formalize the *shape* of the Weil conjectures at
the level of the numerical data they concern: for a `d`-dimensional variety `X` over `𝔽_q`
one has Betti numbers `b i`, inverse roots `α i j` of the characteristic polynomials
`P i` of Frobenius on the `i`-th cohomology group, and point counts
`N n = #X(𝔽_{q^n})` linked by the Grothendieck–Lefschetz trace formula.

The Riemann hypothesis part of the Weil conjectures (Deligne, 1974) is the assertion that
every inverse root occurring in degree `i` has archimedean absolute value `q ^ (i / 2)`.
-/

/-- Numerical zeta-function data attached to a `dim`-dimensional variety over `𝔽_q`:
Betti numbers, the inverse roots of Frobenius in each cohomological degree, the point
counts over the extensions `𝔽_{q ^ n}`, and the Lefschetz trace formula relating them. -/
structure WeilDatum where
  /-- the cardinality of the base field -/
  q : ℕ
  /-- the base field is a genuine finite field -/
  hq : 1 < q
  /-- the dimension of the variety -/
  dim : ℕ
  /-- the Betti numbers -/
  betti : ℕ → ℕ
  /-- the inverse roots of Frobenius acting on the `i`-th cohomology group -/
  root : (i : ℕ) → Fin (betti i) → ℂ
  /-- `pointCount n` is the number of `𝔽_{q ^ n}`-points -/
  pointCount : ℕ → ℕ
  /-- cohomology vanishes above degree `2 * dim` -/
  betti_vanishing : ∀ i, 2 * dim < i → betti i = 0
  /-- the Grothendieck–Lefschetz trace formula -/
  lefschetz : ∀ n : ℕ, 1 ≤ n →
    (pointCount n : ℂ) =
      ∑ i ∈ Finset.range (2 * dim + 1), (-1 : ℂ) ^ i * ∑ j, (root i j) ^ n

/-- The Riemann hypothesis for a zeta datum: every inverse root of Frobenius in
cohomological degree `i` has absolute value `q ^ (i / 2)` (Deligne's theorem, for the
data coming from a smooth projective variety). -/

theorem curve_RH_iff_pointCount_bound {q : ℕ} (hq : 1 < q) {g : ℕ} (α : Fin (2 * g) → ℂ)
    (σ : Equiv.Perm (Fin (2 * g))) (hσ : ∀ j, α j * α (σ j) = (q : ℂ))
    (N : ℕ → ℕ) (hN : ∀ n : ℕ, 1 ≤ n → (N n : ℂ) = (q : ℂ) ^ n + 1 - ∑ j, (α j) ^ n) :
    (curveDatum hq α N hN).RiemannHypothesis ↔
      ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → |(N n : ℝ) - (q : ℝ) ^ n - 1| ≤ C * Real.sqrt q ^ n := by
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hqpos : (0 : ℝ) < q := by exact_mod_cast lt_trans Nat.zero_lt_one hq
  have hsqpos : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
  have hsqsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0
  -- the point count defect is exactly the power sum of the inverse roots
  have key : ∀ n : ℕ, 1 ≤ n → ‖∑ j, (α j) ^ n‖ = |(N n : ℝ) - (q : ℝ) ^ n - 1| := by
    intro n hn
    have h1 : ∑ j, (α j) ^ n = -((((N n : ℝ) - (q : ℝ) ^ n - 1 : ℝ)) : ℂ) := by
      have h2 := hN n hn
      push_cast
      linear_combination h2
    rw [h1, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  rw [curveDatum_riemannHypothesis_iff]
  constructor
  · intro h
    refine ⟨(2 * g : ℕ), fun n hn => ?_⟩
    rw [← key n hn]
    calc ‖∑ j, (α j) ^ n‖ ≤ ∑ j, ‖(α j) ^ n‖ := norm_sum_le _ _
    _ = ∑ _j : Fin (2 * g), Real.sqrt q ^ n := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [norm_pow, h j]
    _ = ((2 * g : ℕ) : ℝ) * Real.sqrt q ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_num
  · rintro ⟨C, hC⟩
    have hbound : ∀ n : ℕ, 1 ≤ n → ‖∑ j, (α j) ^ n‖ ≤ C * Real.sqrt q ^ n := by
      intro n hn
      rw [key n hn]
      exact hC n hn
    have hle : ∀ j, ‖α j‖ ≤ Real.sqrt q :=
      fun j => norm_le_of_powerSum_bound α hsqpos hbound j
    intro j
    have hprod : ‖α j‖ * ‖α (σ j)‖ = (q : ℝ) := by
      rw [← norm_mul, hσ j, Complex.norm_natCast]
    have h1 := hle j
    have h2 := hle (σ j)
    nlinarith [norm_nonneg (α j), norm_nonneg (α (σ j))]

/-- Sanity check: the datum of `ℙ¹` over `𝔽_q` really does count `q ^ n + 1` points. -/
