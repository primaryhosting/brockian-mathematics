import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
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

open Filter MeasureTheory Metric

/-! ## Auxiliary lemmas -/

/-- Superadditivity of `liminf` for two `ℝ≥0∞`-valued sequences. -/

theorem card_mul_le_of_concentration {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : ℕ → Measure X) (E ε : ENNReal) (hE : ∀ n, μ n Set.univ ≤ E)
    (t : Finset X)
    (ht : ∀ x ∈ t, ∀ r > (0 : ℝ), ε ≤ liminf (fun n => μ n (ball x r)) atTop) :
    (t.card : ENNReal) * ε ≤ E := by
  classical
  obtain ⟨r, hr, hdisj⟩ := exists_radius_pairwise_disjoint_ball (s := (t : Set X)) t.finite_toSet
  -- for every `n`, the disjoint balls carry total mass at most `E`
  have hsum : ∀ n, ∑ x ∈ t, μ n (ball x r) ≤ E := by
    intro n
    have hbi : μ n (⋃ x ∈ t, ball x r) = ∑ x ∈ t, μ n (ball x r) :=
      measure_biUnion_finset (fun x hx y hy hxy => hdisj x hx y hy hxy)
        (fun x _ => measurableSet_ball)
    calc ∑ x ∈ t, μ n (ball x r) = μ n (⋃ x ∈ t, ball x r) := hbi.symm
      _ ≤ μ n Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ E := hE n
  calc (t.card : ENNReal) * ε = ∑ _x ∈ t, ε := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ t, liminf (fun n => μ n (ball x r)) atTop :=
          Finset.sum_le_sum (fun x hx => ht x hx r hr)
    _ ≤ liminf (fun n => ∑ x ∈ t, μ n (ball x r)) atTop :=
          sum_liminf_le_liminf_sum t (fun x n => μ n (ball x r))
    _ ≤ liminf (fun _ : ℕ => E) atTop := liminf_le_liminf (by filter_upwards with n using hsum n)
    _ = E := liminf_const E

/-! ## Main result -/

/-- **Uhlenbeck bubbling: finiteness and counting of the blow-up set.**

Let `μ n` be the Yang–Mills energy densities (`|F(A n)|²` measures) of a sequence of connections
on a metric measure space `X`, with uniformly bounded total energy `E < ∞`.  Let `ε > 0` be the
energy quantum (given, e.g., by the `ε`-regularity theorem) and let `S` be the *blow-up set*:
the set of points at which every ball retains asymptotic energy at least `ε`.

Then `S` is finite, and the number of bubbling points is controlled by the energy:
`(#S) * ε ≤ E`.  In particular at most `E / ε` bubbles can form, which is the counting statement
underlying Uhlenbeck's compactness theorem (convergence away from finitely many points). -/
