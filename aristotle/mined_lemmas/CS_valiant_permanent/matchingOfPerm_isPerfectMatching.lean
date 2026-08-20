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

theorem matchingOfPerm_isPerfectMatching (I : Inst)
    (σ : {σ : Equiv.Perm (Fin I.size) // ∀ i, I.edge i (σ i)}) :
    (matchingOfPerm I σ).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  rintro (i | j)
  · refine ⟨Sum.inr (σ.1 i), rfl, ?_⟩
    rintro (a | a) h <;> simp_all [matchingOfPerm]
  · refine ⟨Sum.inl (σ.1.symm j), by simp [matchingOfPerm], ?_⟩
    rintro (a | a) h
    · simp only [matchingOfPerm] at h
      simp [← h]
    · simp [matchingOfPerm] at h

