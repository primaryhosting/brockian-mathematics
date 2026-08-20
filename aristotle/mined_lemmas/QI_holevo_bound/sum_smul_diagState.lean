import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
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

namespace QI

open Finset

/-! ### Classical entropies -/

/-- Shannon entropy of a probability vector, in nats. -/

lemma sum_smul_diagState {ι : Type*} [Fintype ι] (p : ι → ℝ) (r : ι → n → ℝ) :
    (∑ i, (p i : ℂ) • diagState (r i)) = diagState (fun z => ∑ j, p j * r j z) := by
  ext z w
  by_cases h : z = w
  · subst h
    simp [diagState, Matrix.sum_apply, Matrix.diagonal]
  · simp [diagState, Matrix.sum_apply, Matrix.diagonal, h]

/-! ### Commuting ensembles -/

/-- A density matrix which is diagonal in the orthonormal basis given by the columns of the
unitary `U`, with spectrum `r`. An ensemble of such states sharing one `U` is exactly an
ensemble of pairwise commuting density matrices. -/
