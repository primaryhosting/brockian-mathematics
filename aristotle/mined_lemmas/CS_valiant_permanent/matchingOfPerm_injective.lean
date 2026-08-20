/-
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- An instance of the 0/1 permanent problem: a size `n` together with an `n × n`
matrix of bits, viewed equivalently as the adjacency data of a bipartite graph. -/
structure Inst where
  size : ℕ
  edge : Fin size → Fin size → Bool

/-- The 0/1 matrix (over `ℕ`) attached to an instance. -/

theorem matchingOfPerm_injective (I : Inst) : Function.Injective (matchingOfPerm I) := by
  rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
  refine Subtype.ext (Equiv.ext fun i => ?_)
  have h2 : (matchingOfPerm I ⟨τ, hτ⟩).Adj (Sum.inl i) (Sum.inr (σ i)) :=
    h ▸ (rfl : (matchingOfPerm I ⟨σ, hσ⟩).Adj (Sum.inl i) (Sum.inr (σ i)))
  have h3 : τ i = σ i := h2
  exact h3.symm

