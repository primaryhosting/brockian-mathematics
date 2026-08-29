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

lemma sum_partJoint (S : System V) (A : Finset V) :
    ∑ x, ∑ y, partJoint S A x y = 1 := by
  have step : ∀ x1 : {v // v ∈ A} → Bool, ∀ y1 : {v // v ∉ A} → Bool,
      ∑ x2 : {v // v ∈ A} → Bool, ∑ y2 : {v // v ∉ A} → Bool,
        joint S (comb A x1 y1) (comb A x2 y2)
        = ∑ t : V → Bool, joint S (comb A x1 y1) t := by
    intro x1 y1
    exact sum_comb A (fun t => joint S (comb A x1 y1) t)
  calc ∑ x, ∑ y, partJoint S A x y
      = ∑ x1 : {v // v ∈ A} → Bool, ∑ x2 : {v // v ∈ A} → Bool,
          ∑ y1 : {v // v ∉ A} → Bool, ∑ y2 : {v // v ∉ A} → Bool,
            joint S (comb A x1 y1) (comb A x2 y2) := by
        simp only [partJoint, Fintype.sum_prod_type]
    _ = ∑ x1 : {v // v ∈ A} → Bool, ∑ y1 : {v // v ∉ A} → Bool,
          ∑ x2 : {v // v ∈ A} → Bool, ∑ y2 : {v // v ∉ A} → Bool,
            joint S (comb A x1 y1) (comb A x2 y2) := by
        exact Finset.sum_congr rfl fun x1 _ => Finset.sum_comm
    _ = ∑ x1 : {v // v ∈ A} → Bool, ∑ y1 : {v // v ∉ A} → Bool,
          ∑ t : V → Bool, joint S (comb A x1 y1) t := by
        exact Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun y1 _ => step x1 y1
    _ = ∑ s : V → Bool, ∑ t : V → Bool, joint S s t :=
        sum_comb A (fun s => ∑ t : V → Bool, joint S s t)
    _ = 1 := sum_joint S

/-- Effective information across any bipartition is nonnegative. -/
