/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-! ## Complexification -/

/-- Complex conjugation acting on the complexification `ℂ ⊗[ℚ] V` of a `ℚ`-vector space `V`,
as a `ℚ`-linear automorphism. -/

theorem hodgeConjecture_congr (X Y : HodgeDatum) (e : X.V ≃ₗ[ℚ] Y.V)
    (hH : ∀ v : X.V, v ∈ X.hodgeClasses ↔ e v ∈ Y.hodgeClasses)
    (ha : ∀ v : X.V, v ∈ X.alg ↔ e v ∈ Y.alg) :
    HodgeConjecture X ↔ HodgeConjecture Y := by
  constructor
  · intro h w hw
    obtain ⟨v, rfl⟩ := e.surjective w
    exact (ha v).1 (h ((hH v).2 hw))
  · intro h v hv
    exact (ha v).2 (h ((hH v).1 hv))

/-- **Base case: no nonzero Hodge classes.** If the `(p,p)`-part of the Hodge decomposition
vanishes, there are no nonzero Hodge classes and the conjecture holds trivially. -/
