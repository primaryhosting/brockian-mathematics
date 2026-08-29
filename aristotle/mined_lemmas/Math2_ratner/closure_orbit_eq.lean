import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalized here

Ratner's theorems concern a one-parameter unipotent subgroup `{u_t}` of a Lie group `G` acting on
a homogeneous space `G / Γ` for a lattice `Γ`, and assert that

* the closure of every orbit is a homogeneous subset `x · H` for a closed connected subgroup `H`
  (orbit closure theorem), and
* every ergodic `u_t`-invariant probability measure is the homogeneous measure supported on such
  an orbit closure (measure classification).

This file formalizes and proves these two statements for the abelian instance
`G = ℝ²`, `Γ = ℤ²`, `u_t = (t, α t)`, i.e. the linear flow of slope `α` on the two-torus.
Here every element of `G` is unipotent, `G / Γ` is the compact homogeneous space `ℝ²/ℤ²`,
and the two conclusions read:

* `Math2.closure_orbit_eq_coset` (proved in the generality of an arbitrary topological abelian
  group): every orbit closure of a one-parameter subgroup is a coset of one fixed closed
  connected subgroup;
* `Math2.dense_orbit`: for irrational `α` the flow is minimal, so the orbit closures are the whole
  space (`H = ⊤`);
* `Math2.eq_volume_of_invariant`: for irrational `α` the flow is uniquely ergodic, i.e. Haar
  probability measure is the only invariant Borel probability measure — which is the measure
  classification statement in this setting.

The main theorem `Math2.ratner` packages the three statements together.
-/

open MeasureTheory Set Topology
open scoped BoundedContinuousFunction

namespace Math2

noncomputable section

instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The circle `ℝ / ℤ`. -/
abbrev Circle := AddCircle (1 : ℝ)

/-- The two-dimensional torus `ℝ² / ℤ²`, a homogeneous space `G / Γ` with `G = ℝ²`
(a unipotent group) and `Γ = ℤ²` a lattice. -/
abbrev Torus := Circle × Circle

/-- The one-parameter unipotent subgroup `t ↦ (t, α t)` of `ℝ²`, viewed inside the torus. -/

theorem closure_orbit_eq (α : ℝ) (x : Torus) :
    closure (orbit α x) = (fun y => x + y) '' (flowClosure α : Set Torus) :=
  closure_orbit_eq_coset (uflow α) x

/-! ## Minimality for irrational slope -/

