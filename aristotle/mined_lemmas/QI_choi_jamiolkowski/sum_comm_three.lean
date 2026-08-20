import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Statement: CP maps correspond to positive Choi matrices (Choi–Jamiołkowski isomorphism).
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

namespace QI

open Matrix
open scoped ComplexOrder
open scoped MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ`:
the block matrix whose `(a, b)` block is `Φ (single a b 1)`, i.e.
`Choi Φ = (id ⊗ Φ) (|Ω⟩⟨Ω|)` for the unnormalised maximally entangled vector `Ω`. -/

private lemma sum_comm_three {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c := by
  have h1 : ∀ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, f a b c := fun a => Finset.sum_comm
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

omit [Fintype m] [DecidableEq m] in
/-- The Choi matrix determines the map. -/
