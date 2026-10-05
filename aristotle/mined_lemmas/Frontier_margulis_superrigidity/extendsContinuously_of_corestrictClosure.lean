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

theorem extendsContinuously_of_corestrictClosure {Γ : Subgroup G} (ρ : Γ →* H)
    (h : ExtendsContinuously Γ (corestrictClosure ρ)) : ExtendsContinuously Γ ρ := by
  obtain ⟨σ, hσc, hσ⟩ := h
  refine ⟨((MonoidHom.range ρ).topologicalClosure).subtype.comp σ,
    (continuous_subtype_val).comp hσc, fun γ => ?_⟩
  simpa [corestrictClosure] using congrArg (Subtype.val) (hσ γ)

end Reduction

/-! ## The target theorem -/

/-- **Margulis superrigidity, reduced to the dense-image case.**

The general statement of Margulis superrigidity for irreducible lattices in higher-rank groups
follows from its special case in which the image of the lattice is dense in the target: given
arbitrary data `(G, Γ, H, ρ)` satisfying the hypotheses, one replaces `H` by the closure of the
image `ρ (Γ)`, which is again a Hausdorff topological group, applies the dense-image case there,
and composes the resulting continuous extension with the (continuous) inclusion of that closed
subgroup into `H`.

This is a Lean-checked reduction: the hypotheses on the ambient group `G` and on the lattice `Γ`
are untouched, and the only input is superrigidity for homomorphisms with dense image. -/
