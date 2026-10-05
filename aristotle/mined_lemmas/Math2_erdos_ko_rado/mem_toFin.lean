/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math2

/-- Transfer a set of naturals to a set of elements of `Fin n`. -/

private lemma mem_toFin {n : ℕ} {A : Finset ℕ} {i : Fin n} :
    i ∈ toFin n A ↔ (i : ℕ) ∈ A := by
  simp [toFin]

