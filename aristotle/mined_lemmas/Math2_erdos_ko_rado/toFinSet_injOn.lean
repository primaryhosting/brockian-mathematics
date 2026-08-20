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

lemma toFinSet_injOn {n : ℕ} {F : Finset (Finset ℕ)}
    (hsub : ∀ A ∈ F, A ⊆ Finset.range n) :
    Set.InjOn (toFinSet n) F := by
  intro A hA B hB hAB
  ext a
  constructor
  · intro ha
    have han : a < n := Finset.mem_range.1 (hsub A hA ha)
    have : (⟨a, han⟩ : Fin n) ∈ toFinSet n A := mem_toFinSet.2 ha
    rw [hAB] at this
    exact mem_toFinSet.1 this
  · intro ha
    have han : a < n := Finset.mem_range.1 (hsub B hB ha)
    have : (⟨a, han⟩ : Fin n) ∈ toFinSet n B := mem_toFinSet.2 ha
    rw [← hAB] at this
    exact mem_toFinSet.1 this

/-- **Erdős–Ko–Rado theorem.** A `k`-uniform intersecting family of subsets of
`{0, …, n-1}` with `2 * k ≤ n` has at most `(n - 1).choose (k - 1)` members. -/
