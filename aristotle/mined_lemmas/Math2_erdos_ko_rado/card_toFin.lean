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

private lemma card_toFin {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (toFin n A).card = A.card := by
  refine Finset.card_bij (fun i _ => (i : ℕ)) (fun i hi => mem_toFin.1 hi) ?_ ?_
  · intro i _ j _ h
    exact Fin.ext h
  · intro b hb
    have hbn : b < n := Finset.mem_range.1 (hA hb)
    exact ⟨⟨b, hbn⟩, mem_toFin.2 hb, rfl⟩

