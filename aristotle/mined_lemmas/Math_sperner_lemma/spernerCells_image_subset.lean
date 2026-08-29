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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Auxiliary counting lemmas -/

/-- Parity translated into `ZMod 2`. -/

lemma spernerCells_image_subset {J : Finset (Fin (n + 1))} {σ : Finset V}
    (hσ : σ ∈ spernerCells carrier T J) : σ.image c ⊆ J := by
  intro j hj
  obtain ⟨v, hv, hfv⟩ := Finset.mem_image.mp hj
  obtain ⟨-, -, hcar⟩ := Finset.mem_filter.mp hσ
  exact hcar v hv (hfv ▸ hc v)

include hdown in
/-- The doors contained in a fixed cell `σ` are exactly the vertex-deletions of `σ` leaving
the colours `J \ {i₀}`. -/
