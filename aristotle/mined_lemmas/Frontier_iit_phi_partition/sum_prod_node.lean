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

lemma sum_prod_node {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → Bool → ℝ)
    (h : ∀ v, g v true + g v false = 1) : ∑ t : ι → Bool, ∏ v, g v (t v) = 1 := by
  have H := Finset.prod_univ_sum (κ := fun _ : ι => Bool) (fun _ => Finset.univ) g
  rw [Fintype.piFinset_univ] at H
  rw [← H]
  simp [h]

/-- The probability that the system moves from state `s` to state `t` in one step. -/
