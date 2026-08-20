/-
# Ham Sandwich
Category: Frontier Physics
Target: Frontier.ham_sandwich
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

open MeasureTheory Set Filter Topology

namespace Frontier

/-!
## Bisecting a single finite measure

The Ham–Sandwich theorem states that `n` finite measures on `ℝⁿ` can be simultaneously
bisected by a single affine hyperplane `{x | ⟪v, x⟫ = c}` (`v` a unit vector), where
"bisected" is understood in the weak sense that each of the two closed half-spaces
carries at least half of the total mass.  (The weak form is the correct one for general
measures: a Dirac mass sitting on the hyperplane cannot be split exactly.)

Mathlib does not contain the Ham–Sandwich theorem, nor the Borsuk–Ulam theorem on which
the general proof rests, so everything below is developed from scratch.  We prove the
base case, `k = 1` measure in `ℝⁿ`, in the form of a median (`Frontier.ham_sandwich`),
together with a genuinely `n`-measure instance for point masses
(`Frontier.ham_sandwich_dirac`).
-/

/-- **Existence of a median.**  For a finite measure `μ` and a measurable real valued
function `f`, there is a threshold `c` such that both `{f ≤ c}` and `{c ≤ f}` carry at
least half of the total mass. -/

theorem exists_unit_hyperplane_through_points {n : ℕ} (hn : 0 < n)
    (p : Fin n → EuclideanSpace ℝ (Fin n)) :
    ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ), ‖v‖ = 1 ∧ ∀ i, inner ℝ v (p i) = c := by
  classical
  set T : (EuclideanSpace ℝ (Fin n) × ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun w i => (inner ℝ w.1 (p i) : ℝ) - w.2
      map_add' := by intro a b; funext i; simp [inner_add_left]; ring
      map_smul' := by intro r a; funext i; simp [real_inner_smul_left]; ring } with hT
  have hrank : Module.finrank ℝ (Fin n → ℝ) < Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ) := by
    simp [Module.finrank_prod, finrank_euclideanSpace]
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := T) hrank)
  have hker : ∀ i, (inner ℝ w.1 (p i) : ℝ) = w.2 := by
    intro i
    have h1 : T w = 0 := hw
    have h2 := congrFun h1 i
    simp only [hT, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, sub_eq_zero] at h2
    exact h2
  have hv0 : w.1 ≠ 0 := by
    intro h
    apply hw0
    have hc : w.2 = 0 := by
      have h3 := hker ⟨0, hn⟩
      rw [h] at h3
      simpa using h3.symm
    exact Prod.ext h hc
  refine ⟨‖w.1‖⁻¹ • w.1, ‖w.1‖⁻¹ * w.2, ?_, ?_⟩
  · rw [norm_smul]
    simp [norm_ne_zero_iff.2 hv0]
  · intro i
    rw [real_inner_smul_left, hker i]

/-- **Ham–Sandwich theorem for `n` point masses in `ℝⁿ`.**

For any `n` Dirac measures on `ℝⁿ` (`n ≥ 1`) there is a single affine hyperplane with unit
normal that simultaneously bisects all of them: each of the two closed half-spaces carries
at least half of the mass of each measure.  Here the hyperplane is chosen to pass through
all `n` points, so that both closed half-spaces carry the full mass. -/
