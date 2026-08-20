/-
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
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

namespace Math

variable {V : Type*} [DecidableEq V]

/-- The `k`-dimensional faces (as `Finset`s of `k` vertices) occurring in the cells of `K`. -/

theorem exists_rainbow_cell (n : ℕ) (A : Finset ℕ) (K : Finset (Finset V))
    (carr : V → Finset ℕ) (c : V → ℕ)
    (hT : IsTriangulation n A K carr)
    (hc : ∀ s ∈ K, ∀ v ∈ s, c v ∈ carr v) :
    ∃ s ∈ K, s.image c = A := by
  obtain ⟨k, hk⟩ := sperner_lemma n A K carr c hT hc
  have hpos : 0 < (K.filter (fun s => s.image c = A)).card := by omega
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_filter.mp hs with ⟨hsK, hsimg⟩
  exact ⟨s, hsK, hsimg⟩

end Math

