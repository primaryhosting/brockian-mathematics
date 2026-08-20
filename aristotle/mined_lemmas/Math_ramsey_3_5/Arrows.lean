import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Ramsey

/-- A `b`-monochromatic set of vertices for the edge colouring `c`. -/

lemma Arrows.of_subset {c : ℕ → ℕ → Bool} {s s' : Finset ℕ} {p q : ℕ} (hss : s ⊆ s')
    (h : Arrows c s p q) : Arrows c s' p q := by
  rcases h with ⟨t, hts, hcard, hmono⟩ | ⟨t, hts, hcard, hmono⟩
  · exact Or.inl ⟨t, hts.trans hss, hcard, hmono⟩
  · exact Or.inr ⟨t, hts.trans hss, hcard, hmono⟩

/-- Adjoining the vertex `v` to a monochromatic clique inside its `b`-neighbourhood. -/
