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

set_option grind.warning false

namespace Phys

/-- The Kosterlitz–Thouless transition temperature of the 2D XY model with spin
stiffness (coupling) `J`, in units where the Boltzmann constant is `1`:
`T_BKT = π J / 2`. -/

lemma log_ratio_pos {L a : ℝ} (ha : 0 < a) (hL : a < L) : 0 < Real.log (L / a) := by
  have h1 : 1 < L / a := (one_lt_div ha).2 hL
  exact Real.log_pos h1

/-- **Berezinskii–Kosterlitz–Thouless topological phase transition of the 2D XY
model.**

For a two-dimensional XY model with spin stiffness `J > 0`, vortex core size
`a > 0` and linear system size `L > a`, the single-vortex free energy
`F(T) = (π J - 2 T) log (L / a)` changes sign exactly at the BKT temperature
`T_BKT = π J / 2`:

* for `T < T_BKT` the free energy cost of a free vortex is strictly positive, so
  isolated vortices are suppressed (bound vortex–antivortex pairs, topologically
  ordered / quasi-long-range-ordered phase);
* at `T = T_BKT` the cost vanishes;
* for `T > T_BKT` the cost is strictly negative, so free vortices proliferate and
  destroy quasi-long-range order (disordered phase).

Moreover `F` is strictly decreasing in `T`, the transition temperature is
strictly positive, and at the transition the spin-correlation exponent takes the
universal value `η(T_BKT) = 1/4`, equivalently the reduced stiffness jumps by the
universal amount `J / T_BKT = 2 / π`. -/
