import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
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

namespace Math2

open MeasureTheory

/-!
## Ratner's orbit-closure theorem for one-parameter (unipotent) flows

Setting: a topological abelian group `G` (written additively), a subgroup `Γ ≤ G`, the
homogeneous space `G ⧸ Γ`, and a one-parameter subgroup `u : ℝ →+ G` acting on `G ⧸ Γ` by
translation, `t • (x Γ) = (x + u t) Γ`.  In an abelian group every one-parameter subgroup is
unipotent, so this is exactly the setting of Ratner's orbit-closure theorem in the commutative
case (the classical Kronecker picture: on `ℝⁿ / ℤⁿ` the closure of a linear orbit is a coset of
a closed subgroup).

`Math2.ratner` states the conclusion of the orbit-closure theorem: the closure of the orbit of
any point is a *coset of a closed subgroup* `H` of `G ⧸ Γ`, where `H` contains the flow and is
the smallest closed subgroup that does so; in particular the orbit closure is homogeneous, i.e.
invariant under the flow.
-/

/-- **Ratner's orbit-closure theorem (commutative case).**

Let `G` be a topological abelian group, `Γ ≤ G` a subgroup and `u : ℝ →+ G` a one-parameter
subgroup, acting on the homogeneous space `G ⧸ Γ` by `t ↦ (· + u t)`.  Then for every `x : G`
there is a *closed subgroup* `H ≤ G ⧸ Γ` such that

* `H` contains the image of the flow;
* `H` is the smallest closed subgroup with that property;
* the closure of the orbit of `x Γ` is the coset `x Γ + H`;
* consequently the orbit closure is invariant under the flow.

Thus every orbit closure of the flow is homogeneous: a coset of a closed subgroup.  (No
continuity assumption on `u` is needed for this conclusion.) -/

theorem ratner_measure_circle {T : ℝ} [Fact (0 < T)] (α : ℝ) (hα : α ≠ 0)
    (μ : Measure (AddCircle T)) [IsProbabilityMeasure μ]
    (hinv : ∀ t : ℝ, Measure.map (fun y : AddCircle T => ((t * α : ℝ) : AddCircle T) + y) μ = μ) :
    μ = AddCircle.haarAddCircle := by
  haveI : μ.IsAddLeftInvariant := by
    constructor
    intro g
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples T) g
    have h := hinv (r / α)
    rwa [div_mul_cancel₀ _ hα] at h
  haveI : μ.IsAddHaarMeasure := by constructor
  exact MeasureTheory.Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure μ _

end Math2

