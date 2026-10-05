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

theorem hodgeConjecture_of_rank_le_one (X : HodgeDatum)
    (hrank : Module.rank ℚ X.V ≤ 1) (hne : X.alg ≠ ⊥) : HodgeConjecture X := by
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.1 hrank
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨r, hr⟩ := hv₀ a
  have hr0 : r ≠ 0 := by
    rintro rfl; exact ha0 (by simpa using hr.symm)
  have hv₀alg : v₀ ∈ X.alg := by
    have : v₀ = r⁻¹ • a := by
      rw [← hr, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [this]
    exact X.alg.smul_mem _ ha
  intro v _
  obtain ⟨s, hs⟩ := hv₀ v
  rw [← hs]
  exact X.alg.smul_mem _ hv₀alg

/-! ## Non-vacuity: the Hodge datum of a point -/

/-- The Hodge datum of a point (equivalently, `H^0` of a connected smooth projective
variety): `V = ℚ`, `p = 0`, the whole complexification sits in bidegree `(0,0)`, and the
fundamental class generates the algebraic classes. -/
