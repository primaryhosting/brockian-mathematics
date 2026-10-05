import Mathlib
/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Finset Matrix

section Rearrangement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Value of the bilinear form `M ↦ ∑ j, ∑ k, M j k * (a j * b k)` at a permutation matrix. -/

lemma Monovary.of_antitone {a b : ι → ℝ} [LinearOrder ι] (ha : Antitone a) (hb : Antitone b) :
    Monovary a b := by
  intro i j hij
  rcases le_total j i with h | h
  · exact ha h
  · exact absurd (hb h) (not_le.2 hij)

end Rearrangement

section Weights

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
  {A B : Matrix n n 𝕜}

/-- The unitary `W = U⋆ V` relating the eigenvector bases of `A` and `B`. -/
