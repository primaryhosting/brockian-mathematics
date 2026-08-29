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

lemma sum_comb (A : Finset V) (F : (V → Bool) → ℝ) :
    ∑ a : {v // v ∈ A} → Bool, ∑ b : {v // v ∉ A} → Bool, F (comb A a b)
      = ∑ s : V → Bool, F s := by
  have H : ∑ z : ({v // v ∈ A} → Bool) × ({v // v ∉ A} → Bool), F (comb A z.1 z.2)
      = ∑ s : V → Bool, F s :=
    Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (· ∈ A) (fun _ => Bool)).symm _ _ (fun _ => rfl)
  rw [Fintype.sum_prod_type] at H
  exact H

/-- The transition probabilities of independently updating binary nodes sum to one. -/
