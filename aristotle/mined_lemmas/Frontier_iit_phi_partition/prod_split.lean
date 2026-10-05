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

lemma prod_split (A : Finset V) (F : V → ℝ) :
    (∏ v : {v // v ∈ A}, F v) * (∏ v : {v // v ∉ A}, F v) = ∏ v, F v := by
  have h1 : (∏ v : {v // v ∈ A}, F v) = ∏ v ∈ A, F v := Finset.prod_coe_sort A F
  have h2 : (∏ v : {v // v ∉ A}, F v) = ∏ v ∈ Aᶜ, F v := by
    rw [← Finset.prod_coe_sort Aᶜ F]
    exact Fintype.prod_equiv (Equiv.subtypeEquivRight (by simp)) _ _ (fun _ => rfl)
  rw [h1, h2, Finset.prod_mul_prod_compl]

/-- If no connection of the system crosses the bipartition `{A, Aᶜ}`, then the effective
information across that bipartition vanishes. -/
