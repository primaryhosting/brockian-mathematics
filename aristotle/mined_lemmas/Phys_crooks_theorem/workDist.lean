import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
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

/-- The work distribution associated to a path measure `p` on a finite set of
microscopic trajectories `Γ`, with work functional `W`: the probability of
observing work value `w` is the total weight of the trajectories realizing it. -/

noncomputable def workDist {Γ : Type*} [Fintype Γ] (W : Γ → ℝ) (p : Γ → ℝ) (w : ℝ) : ℝ :=
  ∑ γ ∈ Finset.univ.filter (fun γ => W γ = w), p γ

/-- **Key intermediate lemma (path-reversal reindexing).**
If `R` is the time-reversal involution on trajectories and it flips the sign of the
work, then summing the reverse-process weights of the reversals of the trajectories
of work `w` computes exactly the reverse work distribution at `-w`. -/
