import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
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

open Set MeasureTheory Filter Topology

/-!
## The classical fluctuation–dissipation relation

Let `C t = ⟨A(0) A(t)⟩` be the equilibrium autocorrelation function of an observable `A`
in a system at inverse temperature `β`.  The (classical, Kubo) fluctuation–dissipation

theorem states that the linear response function to a perturbation `-f(t) A` is

  `χ(t) = -β * dC/dt (t)`   for `t > 0`.

Everything below is stated for an arbitrary correlation function `C` with derivative `C'`,
with the fluctuation–dissipation relation `χ = -β C'` imposed as a hypothesis; the content
of the results is the *sum rule* obtained by integrating the relation, i.e. the statement
that the static (zero-frequency) susceptibility is `β` times the equal-time fluctuation.
-/

/-- **Finite-time fluctuation–dissipation sum rule.**

If the response function `χ` is related to the equilibrium autocorrelation function `C`
by the fluctuation–dissipation relation `χ t = -β * C' t` (with `C'` the derivative of `C`),
then the response integrated up to time `T` measures the decay of the correlation:

`∫_0^T χ(t) dt = β * (C 0 - C T)`. -/
