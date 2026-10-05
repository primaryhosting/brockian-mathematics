/-
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped NNReal ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Uhlenbeck bubbling: quantization of the blow-up set

For a sequence of Yang–Mills connections `A n` on a bundle over a Riemannian manifold `X`
with uniformly bounded Yang–Mills energy `E`, Uhlenbeck's compactness theorem says that,
after gauge transformations and passing to a subsequence, the connections converge smoothly
away from a finite "bubbling" set of points, and at each bubbling point at least a fixed
quantum `ε₀ > 0` of energy is lost.

The genuinely analytic inputs of that theorem are (i) Uhlenbeck's gauge fixing / removable
singularity theorem and (ii) the ε-regularity estimate, which produces the energy quantum
`ε₀`.  What is formalized here is the *bubbling / energy-quantization* mechanism itself,
stated for the sequence of energy densities: the energy densities of the connections are
encoded as a sequence of Borel measures `μ n` on `X` (`μ n = |F_{A n}|² dvol`), the uniform
energy bound is `μ n univ ≤ E`, and the bubbling set is the set of points at which, at every
scale, at least the energy quantum `ε₀` persists in the limit.

The theorem proved below is the resulting reduction: **the bubbling set is finite, and the
number of bubbles times the energy quantum is bounded by the total energy**, i.e. there are
at most `E / ε₀` bubbles.  This is exactly the counting statement used in the Uhlenbeck
compactness theorem to conclude that only finitely many bubbles occur.
-/

namespace Frontier

open MeasureTheory Metric Filter Set

/-- The **bubbling (energy concentration) set** of a sequence of energy measures `μ` at
quantum `ε₀`: the set of points `x` such that at *every* scale `r > 0` the balls `ball x r`
carry, in the limit inferior along the sequence, at least the energy quantum `ε₀`. -/

theorem card_mul_energyQuantum_le {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : ℕ → Measure X) (ε₀ E : ℝ≥0∞)
    (hε₀ : ε₀ ≠ 0) (hε₀top : ε₀ ≠ ⊤) (hbdd : ∀ n, μ n univ ≤ E)
    (S : Finset X) (hS : ↑S ⊆ bubbleSet μ ε₀) :
    (S.card : ℝ≥0∞) * ε₀ ≤ E := by
  obtain ⟨r, hr, hdisj⟩ := exists_pos_radius_pairwiseDisjoint_ball S
  refine ENNReal.le_of_forall_lt_one_mul_le ?_
  intro a ha
  have hlt : a * ε₀ < ε₀ := by
    calc a * ε₀ = ε₀ * a := mul_comm _ _
      _ < ε₀ * 1 := ENNReal.mul_lt_mul_right hε₀ hε₀top ha
      _ = ε₀ := mul_one _
  have hev : ∀ᶠ n in atTop, ∀ x ∈ S, a * ε₀ < μ n (ball x r) := by
    refine (eventually_all_finset S).2 ?_
    intro x hx
    exact eventually_lt_of_lt_liminf (lt_of_lt_of_le hlt (hS hx r hr))
  obtain ⟨n, hn⟩ := hev.exists
  calc a * ((S.card : ℝ≥0∞) * ε₀) = ∑ _x ∈ S, a * ε₀ := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ x ∈ S, μ n (ball x r) := Finset.sum_le_sum fun x hx => (hn x hx).le
    _ = μ n (⋃ x ∈ S, ball x r) :=
        (measure_biUnion_finset hdisj fun _ _ => measurableSet_ball).symm
    _ ≤ μ n univ := measure_mono (subset_univ _)
    _ ≤ E := hbdd n

/-- **Uhlenbeck bubbling: finiteness and quantization of the blow-up set.**

Let `μ n` be the energy densities of a sequence of connections on a metric measure space `X`,
with total energy uniformly bounded by a finite `E`, and let `ε₀` be the (finite, positive)
energy quantum supplied by ε-regularity.  Then the bubbling set — the set of points where at
every scale at least `ε₀` of energy survives in the limit — is finite, and the number of
bubbles satisfies `#bubbles * ε₀ ≤ E`, i.e. there are at most `E / ε₀` bubbles. -/
