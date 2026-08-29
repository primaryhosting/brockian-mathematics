import Mathlib

/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
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

namespace Phys

/-! ## The Kosterlitz–Thouless vortex-unbinding criterion

We formalise the standard energy–entropy argument for the Berezinskii–Kosterlitz–Thouless
(BKT) topological phase transition of the two–dimensional XY model, in units where the
Boltzmann constant is `k_B = 1`.

For a 2D XY model with spin stiffness `J` on a disc of radius `R` with vortex core size `a`,
a single vortex costs energy `π J log (R / a)`, while the number of possible core positions is
`(R / a) ^ 2`, giving entropy `2 log (R / a)`.  The resulting free energy

`F = (π J - 2 T) log (R / a)`

is positive below `T_BKT = π J / 2` (isolated vortices are thermodynamically suppressed and
the vortices remain bound in neutral pairs — the quasi–long-range ordered phase) and negative
above `T_BKT` (free vortices proliferate — the disordered phase).  Exactly at `T_BKT` the free
energy vanishes; this is the transition point.  At the transition the spin-wave correlation
exponent `η(T) = T / (2 π J)` takes the universal value `1/4`.
-/

/-- Energy of a single vortex in a 2D XY model with spin stiffness `J`, in a system of
radius `R` with vortex core size `a`. -/

lemma tendsto_log_ratio_atTop {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun R : ℝ => Real.log (R / a)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp (Filter.tendsto_id.atTop_div_const ha)

/-- **The Berezinskii–Kosterlitz–Thouless topological phase transition of the 2D XY model.**

For a 2D XY model with spin stiffness `J > 0`, vortex core size `a > 0` and system radius
`R > a`, the free energy of a single (unbound) vortex changes sign exactly at the transition
temperature `T_BKT = π J / 2`:

* below `T_BKT` the free energy is positive, so isolated vortices are suppressed (and diverge
  to `+∞` in the thermodynamic limit `R → ∞`): the quasi-long-range ordered phase;
* at `T_BKT` the free energy vanishes: the transition point;
* above `T_BKT` the free energy is negative, so free vortices proliferate (the free energy
  diverges to `-∞` as `R → ∞`): the disordered phase.

Moreover the spin-wave correlation exponent takes the universal Nelson–Kosterlitz value
`η(T_BKT) = 1/4` at the transition. -/
