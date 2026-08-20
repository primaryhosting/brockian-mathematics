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

lemma hasDerivAt_gibbsWeight (β : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) :
    HasDerivAt (fun f => gibbsWeight β E A f i) (β * A i * gibbsWeight β E A f i) f := by
  have h1 : HasDerivAt (fun f : ℝ => -β * (E i - f * A i)) (β * A i) f := by
    have h := (((hasDerivAt_id f).mul_const (A i)).const_sub (E i)).const_mul (-β)
    simpa using h.congr_deriv (by ring)
  simpa [gibbsWeight, mul_comm] using h1.exp

