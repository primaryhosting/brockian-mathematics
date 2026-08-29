import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
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

/-! ## The Kneser graph -/

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are disjoint. -/

lemma kneser_one_chromaticNumber_ge (n : ℕ) :
    (n : ℕ∞) ≤ (kneserGraph n 1).chromaticNumber := by
  refine SimpleGraph.le_chromaticNumber_of_pairwise_adj (ι := Fin n) (by simp)
    (fun i => ⟨{i}, Finset.card_singleton i⟩) ?_
  intro i j hij
  have h1 : ({i} : Finset (Fin n)) ≠ {j} := by simp [hij]
  exact ⟨fun h => h1 (congrArg Subtype.val h), Finset.disjoint_singleton.mpr hij⟩

/-- The base case `k = 1`: the Kneser graph `KG_{n,1}` is the complete graph `K_n`, so its
chromatic number is `n`. -/
