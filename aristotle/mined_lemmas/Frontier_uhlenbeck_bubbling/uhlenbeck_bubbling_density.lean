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

/-!
# Uhlenbeck Bubbling

Concentration–compactness ("bubbling") for a sequence of Yang–Mills energy measures.

Uhlenbeck's compactness theorem is built on two pillars: an `ε`-regularity theorem (a
connection with small local curvature energy is, after a gauge change, controlled in
every Sobolev norm) and the *bubbling* mechanism, which says that a sequence of
connections with uniformly bounded Yang–Mills energy `Λ` can fail to have small local
energy only at **finitely many** points, at most `Λ / ε₀` of them, where `ε₀` is the
threshold of the `ε`-regularity theorem.

This file formalizes the second pillar in the generality in which it is actually used —
i.e. as a statement about the energy measures `μ n = |F_{A_n}|² dvol` alone — and proves
it: the bubbling set is finite, energy is quantized on it (`#bubbles · ε ≤ Λ`), and off
the bubbling set the small-energy hypothesis of `ε`-regularity is available on a fixed
ball along a subsequence.
-/

namespace Frontier

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The **bubbling set** (energy concentration set) at level `ε` of a sequence of energy
measures `μ n`.

In the Yang–Mills setting `μ n` is the energy measure `|F_{A_n}|² dvol` of a sequence of
connections `A_n`, and `ε` is the `ε`-regularity threshold `ε₀` of Uhlenbeck's theorem.
A point `x` lies in the bubbling set when, at *every* scale `r > 0`, at least `ε` of the
energy asymptotically concentrates in the ball `B(x, r)`: these are exactly the points at
which a bubble can form, i.e. the points where `ε`-regularity may fail. -/

theorem uhlenbeck_bubbling_density {vol : Measure X} {e : ℕ → X → ℝ≥0∞}
    {Λ ε : ℝ≥0∞} (hΛ : Λ ≠ ⊤) (hε : ε ≠ 0)
    (hbound : ∀ n : ℕ, ∫⁻ y, e n y ∂vol ≤ Λ) :
    (bubbleSetDensity vol e ε).Finite ∧
      ((bubbleSetDensity vol e ε).ncard : ℝ≥0∞) * ε ≤ Λ := by
  set μ : ℕ → Measure X := fun n => vol.withDensity (e n) with hμ
  have happly : ∀ (n : ℕ) (s : Set X), MeasurableSet s → μ n s = ∫⁻ y in s, e n y ∂vol :=
    fun n s hs => withDensity_apply (e n) hs
  have hbound' : ∀ n : ℕ, μ n Set.univ ≤ Λ := by
    intro n
    rw [happly n _ MeasurableSet.univ, Measure.restrict_univ]
    exact hbound n
  have hset : bubbleSetDensity vol e ε = bubbleSet μ ε := by
    ext x
    simp only [bubbleSetDensity, bubbleSet, Set.mem_setOf_eq]
    refine forall_congr' fun r => ?_
    refine imp_congr_right fun _ => ?_
    simp only [happly _ _ measurableSet_ball]
  obtain ⟨h1, h2, -⟩ := uhlenbeck_bubbling (μ := μ) hΛ hε hbound'
  exact ⟨hset ▸ h1, hset ▸ h2⟩

end Frontier

