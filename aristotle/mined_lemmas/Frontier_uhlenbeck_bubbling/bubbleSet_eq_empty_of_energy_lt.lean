/-
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory Metric Set Filter Function
open scoped ENNReal Topology

/-! ## The Yang–Mills energy

A Yang–Mills field on a manifold `X` is modelled here by its curvature `F : X → V`, a field with
values in a normed space `V` (in the geometric situation, `V` is the space of `𝔤`-valued
two-forms).  Its Yang–Mills energy over a region `s` is `∫_s ‖F‖²`. -/

section Energy

variable {X : Type*} [MeasurableSpace X] {V : Type*} [NormedAddCommGroup V]

/-- The Yang–Mills energy `∫_s ‖F‖²` of a curvature field `F` over the region `s`. -/

theorem bubbleSet_eq_empty_of_energy_lt {V : Type*} [NormedAddCommGroup V]
    (F : ℕ → E4 → V) (eps : ℝ≥0∞)
    (hbdd : ∀ n, energyOn volume (F n) Set.univ < eps) :
    bubbleSet volume F eps = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have h1 : ∀ᶠ n in atTop, eps ≤ energyOn volume (F n) (ball x 1) := hx 1 one_pos
  have h2 : ∀ᶠ n in atTop, energyOn volume (F n) (ball x 1) < eps := by
    filter_upwards with n using lt_of_le_of_lt (energyOn_mono _ _ (subset_univ _)) (hbdd n)
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  exact absurd hn1 (not_le.2 hn2)

/-! ## Conformal invariance of the four-dimensional Yang–Mills energy

The reason bubbles form in dimension four is that the Yang–Mills energy is *conformally
invariant*: rescaling a connection by `λ` leaves its energy unchanged, so energy can be
concentrated into arbitrarily small balls at no cost. -/

section Rescaling

/-- The curvature of the rescaled connection `A_λ(x) = λ · A(λ x)` is `λ² F(λ x)`. -/
