/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Statement: A k-uniform intersecting family on [n] (n≥2k) has size ≤ C(n−1,k−1) (Erdős–Ko–Rado).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Statement: A k-uniform intersecting family on [n] (n≥2k) has size ≤ C(n−1,k−1) (Erdős–Ko–Rado).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Math2

/-- Transfer a set of naturals to a subset of `Fin n`. -/

lemma card_toFinSet {n : ℕ} {A : Finset ℕ} (h : A ⊆ Finset.range n) :
    (toFinSet n A).card = A.card := by
  apply Finset.card_bij (fun (i : Fin n) _ => (i : ℕ))
  · intro i hi
    exact mem_toFinSet.1 hi
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro a ha
    have han : a < n := Finset.mem_range.1 (h ha)
    exact ⟨⟨a, han⟩, mem_toFinSet.2 ha, rfl⟩

