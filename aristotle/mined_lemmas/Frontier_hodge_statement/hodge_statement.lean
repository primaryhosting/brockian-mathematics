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

theorem hodge_statement :
    (∀ X : HodgeDatum, HodgeConjecture X ↔ X.hodgeClasses = X.alg) ∧
    (HodgeConjecture pointDatum) ∧
    (∀ (X : HodgeDatum) (s : Set X.V), Submodule.span ℚ s = X.hodgeClasses →
      (∀ v ∈ s, v ∈ X.alg) → HodgeConjecture X) ∧
    (∀ (X Y : HodgeDatum) (e : X.V ≃ₗ[ℚ] Y.V),
      (∀ v : X.V, v ∈ X.hodgeClasses ↔ e v ∈ Y.hodgeClasses) →
      (∀ v : X.V, v ∈ X.alg ↔ e v ∈ Y.alg) →
      (HodgeConjecture X ↔ HodgeConjecture Y)) ∧
    (∀ X : HodgeDatum, X.Hpq ((X.p : ℤ), (X.p : ℤ)) = ⊥ → HodgeConjecture X) ∧
    (∀ X : HodgeDatum, Module.rank ℚ X.V ≤ 1 → X.alg ≠ ⊥ → HodgeConjecture X) :=
  ⟨hodgeConjecture_iff_eq, hodgeConjecture_pointDatum, hodgeConjecture_of_span,
    hodgeConjecture_congr, hodgeConjecture_of_Hpp_eq_bot, hodgeConjecture_of_rank_le_one⟩

end Frontier

