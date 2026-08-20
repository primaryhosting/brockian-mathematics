import Mathlib
/-!
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE FILE HEADER.  Lean 4 requires `import` to be the very first command of a
module, so the requested `/-! ... -/` module docstring is placed immediately after the
single `import Mathlib` line rather than before it; its text is otherwise verbatim.
-/

open scoped BigOperators

namespace Frontier

/-! ## The superrigidity extension property

Margulis superrigidity says, for `G` a semisimple Lie group of real rank `≥ 2`, `Γ ≤ G` an
irreducible lattice and `π : Γ → H` a homomorphism into a simple algebraic group with
unbounded Zariski-dense image, that `π` is the restriction of a *continuous* homomorphism
`G → H`.  The predicate below isolates the conclusion of that theorem: a homomorphism
defined on the lattice extends to a continuous homomorphism of the ambient group.
-/

/-- The conclusion of a superrigidity statement, in additive notation: a homomorphism `π`
defined on a lattice `L` (mapped into the ambient group `G` by the inclusion `ι`) is the
restriction along `ι` of a continuous homomorphism `G → H`. -/

theorem eq_of_dense_range {L G H : Type*} [AddGroup L] [AddGroup G] [AddGroup H]
    [TopologicalSpace G] [TopologicalSpace H] [T2Space H] (ι : L →+ G)
    (hd : Dense (Set.range ι)) {ρ σ : G →+ H} (hρ : Continuous ρ) (hσ : Continuous σ)
    (h : ∀ v : L, ρ (ι v) = σ (ι v)) : ρ = σ := by
  have hfun : (ρ : G → H) = (σ : G → H) :=
    Continuous.ext_on hd hρ hσ (by rintro _ ⟨v, rfl⟩; exact h v)
  exact DFunLike.ext _ _ fun x => congrFun hfun x

/-- The standard lattice `ℤ ^ n` inside `ℝ ^ n`, as the inclusion homomorphism. -/
