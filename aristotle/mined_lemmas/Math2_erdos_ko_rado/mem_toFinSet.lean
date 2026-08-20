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

lemma mem_toFinSet {n : ℕ} {A : Finset ℕ} {i : Fin n} :
    i ∈ toFinSet n A ↔ (i : ℕ) ∈ A := by
  simp [toFinSet]

