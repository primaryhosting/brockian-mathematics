import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Frontier

open SimpleGraph Finset

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {A : Finset (Fin n) // A.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`, and two
distinct such subsets are adjacent when they are disjoint. -/

def kneserIsoTop (n : ℕ) : kneserGraph n 1 ≃g (⊤ : SimpleGraph (Fin n)) where
  toFun A := A.1.min' (kneser_vertex_nonempty le_rfl A)
  invFun a := ⟨{a}, Finset.card_singleton a⟩
  left_inv := by
    rintro ⟨A, hA⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA
    simp
  right_inv := by
    intro a; simp
  map_rel_iff' := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hB
    simp [kneserGraph, Subtype.ext_iff]

/-! ## Base case `n = 2k`: the Kneser graph is a perfect matching -/

/-- For `1 ≤ k` and `n = 2k` the Kneser graph has an edge, hence is not `1`-colourable. -/
