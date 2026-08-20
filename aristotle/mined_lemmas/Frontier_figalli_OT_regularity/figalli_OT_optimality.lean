/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
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

namespace Frontier

/-!
## Setting

We work in the standard Kantorovich-duality framework for optimal transport with a
general cost `c : X → Y → ℝ`.

A pair of potentials `(u, v)` is *admissible* when `u x + v y ≤ c x y` for all `x, y`
(this is the constraint set of the dual Kantorovich problem). The *contact set*
(equivalently, the graph of the `c`-subdifferential of `u`) is the set of pairs where
equality holds; any transport plan that is optimal for `c` is supported in it, and an
optimal transport *map* `T` is precisely a selection of the contact fibers.

The regularity theory of Ma–Trudinger–Wang, Loeper and Figalli (Figalli, Kim, McCann,
Loeper, De Philippis–Figalli) shows that under the MTW condition `(A3w)` together with
suitable convexity of the domains and boundedness of the densities, the `c`-subdifferential
of a `c`-convex Kantorovich potential is *single valued*, i.e. every contact fiber is a
singleton. Below, that single-valuedness is taken as the hypothesis `hT`, and the theorem
`Frontier.figalli_OT_regularity` is the Lean-checked reduction from that hypothesis to
continuity of the optimal transport map: single-valuedness of the contact fibers plus
compactness of the target and continuity of the data force the transport map to be
continuous.

`Frontier.figalli_OT_optimality` records that such a map is indeed an optimal transport
map (it minimises the transport cost among all maps pushing `μ` to `ν`), and
`Frontier.figalli_OT_regularity_example` checks that the hypotheses are non-vacuous on a
genuine quadratic-cost example.
-/

section Contact

variable {X Y : Type*}

/-- Admissible pair of Kantorovich potentials for the cost `c`: the dual constraint
`u x + v y ≤ c x y`. -/

theorem figalli_OT_optimality {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {c : X → Y → ℝ} {u : X → ℝ} {v : Y → ℝ} (hpair : IsKantorovichPotentials c u v)
    {mu : MeasureTheory.Measure X} {nu : MeasureTheory.Measure Y} {T S : X → Y}
    (hTm : AEMeasurable T mu) (hSm : AEMeasurable S mu)
    (hTpush : mu.map T = nu) (hSpush : mu.map S = nu)
    (hcontact : ∀ x : X, (x, T x) ∈ contactSet c u v)
    (hu : MeasureTheory.Integrable u mu) (hv : MeasureTheory.Integrable v nu)
    (hcS : MeasureTheory.Integrable (fun x : X => c x (S x)) mu) :
    ∫ x : X, c x (T x) ∂mu ≤ ∫ x : X, c x (S x) ∂mu := by
  -- `v ∘ T` and `v ∘ S` are integrable and have the same integral, namely `∫ v ∂ν`.
  have hvT : MeasureTheory.Integrable (fun x : X => v (T x)) mu := by
    have h : MeasureTheory.Integrable (v ∘ T) mu := by
      rw [← MeasureTheory.integrable_map_measure
        (by rw [hTpush]; exact hv.aestronglyMeasurable) hTm, hTpush]
      exact hv
    exact h
  have hvS : MeasureTheory.Integrable (fun x : X => v (S x)) mu := by
    have h : MeasureTheory.Integrable (v ∘ S) mu := by
      rw [← MeasureTheory.integrable_map_measure
        (by rw [hSpush]; exact hv.aestronglyMeasurable) hSm, hSpush]
      exact hv
    exact h
  have hintT : ∫ x : X, v (T x) ∂mu = ∫ y : Y, v y ∂nu := by
    rw [← hTpush]
    exact (MeasureTheory.integral_map hTm
      (by rw [hTpush]; exact hv.aestronglyMeasurable)).symm
  have hintS : ∫ x : X, v (S x) ∂mu = ∫ y : Y, v y ∂nu := by
    rw [← hSpush]
    exact (MeasureTheory.integral_map hSm
      (by rw [hSpush]; exact hv.aestronglyMeasurable)).symm
  have hTeq : ∫ x : X, c x (T x) ∂mu = ∫ x : X, u x ∂mu + ∫ y : Y, v y ∂nu := by
    have : (fun x : X => c x (T x)) = fun x : X => u x + v (T x) := by
      funext x; exact (hcontact x).symm
    rw [this, MeasureTheory.integral_add hu hvT, hintT]
  have hSle : ∫ x : X, u x ∂mu + ∫ y : Y, v y ∂nu ≤ ∫ x : X, c x (S x) ∂mu := by
    rw [← hintS, ← MeasureTheory.integral_add hu hvS]
    exact MeasureTheory.integral_mono (hu.add hvS) hcS fun x => hpair x (S x)
  rw [hTeq]
  exact hSle

/-!
## A non-vacuous instance

We check the hypotheses of `figalli_OT_regularity` on a genuine quadratic-cost example:
`X = [0,1]`, `Y = [1,2]`, `c x y = (x - y)^2 / 2`, with the Kantorovich potentials
`u x = -x`, `v y = y - 1/2`.  Here the contact fiber over `x` is exactly `{x + 1}`, so the
optimal transport map is the translation `x ↦ x + 1`, and the theorem yields its
continuity.
-/

/-- The translation `x ↦ x + 1` as a map `[0,1] → [1,2]`. -/
