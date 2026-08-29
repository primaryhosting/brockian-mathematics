import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

variable {N M : ℕ}

/-- A linear map between matrix algebras `M_N(ℂ) → M_M(ℂ)`. -/
abbrev MatMap (N M : ℕ) : Type :=
  Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin M) (Fin M) ℂ

/-- The amplification `id_{M_k} ⊗ Φ`, acting on `k × k` block matrices with blocks in
`M_N(ℂ)` by applying `Φ` to each block. -/

private lemma sum_rev3 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid δ]
    (f : α → β → γ → δ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  rw [show (∑ b, ∑ a, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c from
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
  exact Finset.sum_comm

/-- Every positive semidefinite matrix factors as `Bᴴ * B`. -/
