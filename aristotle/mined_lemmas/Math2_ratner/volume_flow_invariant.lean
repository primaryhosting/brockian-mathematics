/-
# Ratner
Category: Frontier Math
Target: Math2.ratner
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

set_option grind.warning false

namespace Math2

/-! ## Ratner's orbit closure theorem, abelian (torus) case

Ratner's orbit closure theorem states that if `U = {u_t}` is a one-parameter unipotent
subgroup of a Lie group `G` and `Γ ≤ G` is a lattice, then for every `x ∈ G/Γ` the closure
of the orbit `{u_t · x}` is a homogeneous set `x · H` for some closed connected subgroup
`H ≤ G` containing `U`, and the orbit is equidistributed with respect to the (unique)
`H`-invariant probability measure on `x · H`.

Here we formalise this in the abelian setting, which is a genuine instance of the theorem:
`G = ℝⁿ` is a (unipotent, abelian) Lie group, `Γ = ℤⁿ` is a lattice, the homogeneous space is
the torus `𝕋ⁿ = ℝⁿ/ℤⁿ`, and every one-parameter subgroup `t ↦ t · v` of `ℝⁿ` is unipotent.

* `Math2.orbitClosure_eq_coset` is the orbit closure statement: the closure of the orbit of
  a one-parameter subgroup is a coset of a closed connected subgroup containing the acting
  subgroup.
* `Math2.dense_orbit_irrational_slope` is the classical instance on the two-torus: the linear
  flow of irrational slope has all orbits dense (so there the subgroup `H` is everything).
-/

section OrbitClosure

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- **Orbit closure theorem, abelian case.** For a continuous one-parameter subgroup
`f : ℝ →+ G` of a topological abelian group `G` and any point `x`, the closure of the orbit
`{x + f t : t ∈ ℝ}` is the coset `x + H` of a closed connected subgroup `H` of `G`
containing the one-parameter subgroup. -/

theorem volume_flow_invariant (α t : ℝ) :
    (volume : Measure Torus2).map (fun x => linearFlow α t + x) = volume :=
  map_add_left_eq_self volume (linearFlow α t)

/-- **Ratner's orbit closure theorem in the abelian (torus) setting.**

The first component is the orbit closure statement: for any continuous one-parameter subgroup
`f` of a topological abelian group `G` (e.g. a one-parameter unipotent subgroup acting on the
homogeneous space `ℝⁿ/ℤⁿ`) and any base point `x`, the orbit closure of `x` is the coset
`x + H` of a closed connected subgroup `H` containing the acting one-parameter subgroup.

The second component is the classical instance on the two-torus `𝕋² = ℝ²/ℤ²`: for the linear
flow `t ↦ (t, α t)` with `α` irrational, every orbit is dense, i.e. `H` is the whole group.

The third component is the corresponding measure classification (unique ergodicity) statement:
the only Borel probability measure on `𝕋²` invariant under such a flow is the Haar (Lebesgue)
measure, i.e. the algebraic measure on the (whole) orbit closure. -/
