import Mathlib
/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

namespace Frontier

/-! ## Part 1: elementary finite information theory -/

/-- Kullback–Leibler divergence of `p` from `q`, over a finite alphabet.
With the `Real.log` conventions, terms with `p i = 0` contribute `0`. -/

noncomputable def partJoint (S : System V) (A : Finset V)
    (x : (({v // v ∈ A} → Bool) × ({v // v ∈ A} → Bool)))
    (y : (({v // v ∉ A} → Bool) × ({v // v ∉ A} → Bool))) : ℝ :=
  joint S (comb A x.1 y.1) (comb A x.2 y.2)

/-- Effective information across the bipartition `{A, Aᶜ}`: the mutual information between
the trajectory (present and next state) of the part `A` and the trajectory of its complement,
with the present global state drawn uniformly. It vanishes exactly when the two parts of the
system evolve independently of one another. -/
