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

/-! ## The two–dimensional XY model -/

/-- Sites of the two-dimensional square lattice `ℤ²`. -/
abbrev Site : Type := ℤ × ℤ

/-- The XY-model Hamiltonian `H(θ) = -J ∑_{⟨xy⟩} cos (θ x - θ y)` for a finite collection
of nearest-neighbour bonds. -/

private theorem tendsto_exp_inv_sqrt_mul_pow {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Filter.Tendsto (fun u : ℝ => Real.exp (b / Real.sqrt u) * u ^ n)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  have key : Filter.Tendsto
      (fun v : ℝ => b ^ (2 * n) * (Real.exp v / v ^ (2 * n))) Filter.atTop Filter.atTop := by
    refine Filter.Tendsto.const_mul_atTop (by positivity) ?_
    exact Real.tendsto_exp_div_pow_atTop (2 * n)
  have hcomp := key.comp (tendsto_inv_sqrt hb)
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : (0 : ℝ) < u := hu
  have hs : Real.sqrt u > 0 := Real.sqrt_pos.2 hu'
  have hsq : (Real.sqrt u) ^ (2 * n) = u ^ n := by
    rw [pow_mul, Real.sq_sqrt hu'.le]
  simp only [Function.comp_apply]
  rw [div_pow, hsq]
  field_simp

/-! ## The BKT transition -/

/-- **The Berezinskii–Kosterlitz–Thouless topological phase transition of the two-dimensional
XY model.**

For a ferromagnetic coupling `J > 0` the model, whose Hamiltonian
`H(θ) = -J ∑_{⟨xy⟩} cos(θ_x - θ_y)` is invariant under the global rotation `θ ↦ θ + α`,
carries a `ℤ`-valued topological charge (the plaquette vorticity, quantised in units of `2π`).
There is a unique critical temperature `T_c = πJ/2` such that:

* below `T_c` the free energy `F = πJ log L - T log L²` of an isolated vortex diverges to
  `+∞` with the system size: isolated vortices are suppressed and vortices stay bound in
  neutral pairs (quasi-long-range order, power-law correlations with exponent
  `η(T) = T/(2πJ)`);
* above `T_c` it diverges to `-∞`: free vortices proliferate and destroy the quasi-order
  (exponential decay with correlation length `ξ`);
* at `T = T_c` energy and entropy balance exactly, `F ≡ 0`, the exponent takes the universal
  value `η(T_c) = 1/4` and the stiffness-to-temperature ratio the universal value `2/π`;
* the correlation length has an essential singularity at `T_c`: it diverges as `T ↓ T_c`
  faster than any power of `T - T_c`. -/
