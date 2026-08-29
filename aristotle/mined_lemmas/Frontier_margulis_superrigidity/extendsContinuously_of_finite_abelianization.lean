import Mathlib

/-!
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
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

namespace Frontier

universe u

/-! ## The conclusion of superrigidity -/

/-- The conclusion of Margulis superrigidity for a homomorphism `ρ : Γ →* H` defined on a
subgroup `Γ` of a topological group `G`: `ρ` is the restriction of a continuous homomorphism
`G →* H`. -/

theorem extendsContinuously_of_finite_abelianization {Γ : Subgroup G}
    (hab : Finite (Abelianization Γ)) [CommGroup H] (htf : Monoid.IsTorsionFree H)
    (ρ : Γ →* H) : ExtendsContinuously Γ ρ := by
  have hone : ∀ γ : Γ, ρ γ = 1 := by
    intro γ
    have hfin : Finite (MonoidHom.range (Abelianization.lift ρ)) := by
      have := hab
      exact Set.Finite.to_subtype (Set.toFinite _)
    have hmem : ρ γ ∈ MonoidHom.range (Abelianization.lift ρ) :=
      ⟨Abelianization.of γ, by simp⟩
    by_contra hne
    refine htf _ hne ?_
    have : IsOfFinOrder (⟨ρ γ, hmem⟩ : MonoidHom.range (Abelianization.lift ρ)) :=
      isOfFinOrder_of_finite _
    exact (isOfFinOrder_iff_pow_eq_one.mpr (by
      obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp this
      exact ⟨n, hn, by
        have := congrArg (Subtype.val) hpow
        simpa using this⟩))
  exact ⟨1, continuous_const, fun γ => (hone γ).symm⟩

end BaseCases

/-! ## Reduction to the dense-image case -/

section Reduction

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H]

/-- The corestriction of `ρ : Γ →* H` to the closure of its image. -/
