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

lemma gibbsPartition_pos (β : ℝ) (E A : ι → ℝ) (f : ℝ) : 0 < gibbsPartition β E A f :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- **Static fluctuation–dissipation theorem.**  For a finite classical system in Gibbs
equilibrium at inverse temperature `β`, with the observable `A` coupled to a field `f`
(Hamiltonian `E - f A`), the susceptibility `d⟨A⟩_f / df` equals `β` times the equilibrium
fluctuation `⟨A²⟩_f - ⟨A⟩_f²` of `A`.  This is the fluctuation–dissipation relation itself,
derived rather than assumed. -/
