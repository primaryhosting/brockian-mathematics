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

lemma card_part_add (A : Finset V) :
    Fintype.card {v // v ∈ A} + Fintype.card {v // v ∉ A} = Fintype.card V := by
  have h1 : A.card ≤ Fintype.card V := by simpa using Finset.card_le_univ A
  simp [Fintype.card_subtype_compl, Fintype.card_coe]
  omega

/-- Splitting a product over the nodes into the part `A` and its complement. -/
