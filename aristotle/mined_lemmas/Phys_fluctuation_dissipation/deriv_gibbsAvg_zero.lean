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

theorem deriv_gibbsAvg_zero (β : ℝ) (E A : ι → ℝ) :
    deriv (fun f => gibbsAvg β E A f A) 0
      = β * (gibbsAvg β E A 0 (fun i => A i ^ 2) - (gibbsAvg β E A 0 A) ^ 2) :=
  (susceptibility_eq_beta_mul_variance β E A 0).deriv

end Gibbs

end Phys

