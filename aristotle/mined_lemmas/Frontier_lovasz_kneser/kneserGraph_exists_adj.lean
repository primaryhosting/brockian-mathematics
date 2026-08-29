/-
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of an
`n`-element set. -/
abbrev KneserVertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`, and two
distinct such subsets are adjacent when they are disjoint. -/

lemma kneserGraph_exists_adj (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ s t : KneserVertex n k, (kneserGraph n k).Adj s t := by
  classical
  have h1 : ∀ x ∈ Finset.range k, x < n := by intro x hx; simp at hx; omega
  have h2 : ∀ x ∈ Finset.Ico k (2 * k), x < n := by intro x hx; simp at hx; omega
  refine ⟨⟨(Finset.range k).attachFin h1, by rw [Finset.card_attachFin, Finset.card_range]⟩,
    ⟨(Finset.Ico k (2 * k)).attachFin h2, by rw [Finset.card_attachFin, Nat.card_Ico]; omega⟩, ?_⟩
  have hdisj : Disjoint ((Finset.range k).attachFin h1) ((Finset.Ico k (2 * k)).attachFin h2) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp [Finset.mem_attachFin] at hx hx'
    omega
  refine ⟨?_, hdisj⟩
  intro hEq
  have hmem : (⟨0, by omega⟩ : Fin n) ∈ (Finset.range k).attachFin h1 := by
    simp [Finset.mem_attachFin]; omega
  have := Finset.disjoint_left.mp hdisj hmem
  rw [Subtype.ext_iff] at hEq
  simp only at hEq
  exact this (hEq ▸ hmem)

