import Mathlib
/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_k ⊗ Φ` of a linear map `Φ` between matrix algebras:
it applies `Φ` to each `n × n` block of a `(k × n) × (k × n)` matrix. -/

private lemma sum_triple_rev {α β γ M : Type} [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M] (f : α → β → γ → M) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c := by
  rw [show (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ c, ∑ b, f a b c from
    Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

section Kraus

variable {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}

/-- The (unnormalized) maximally entangled state `|Ω⟩⟨Ω|` on `n ⊗ n`, written as
`WᴴW` so that it is manifestly positive semidefinite. -/
