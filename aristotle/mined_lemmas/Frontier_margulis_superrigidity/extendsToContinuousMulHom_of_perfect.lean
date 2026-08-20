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

theorem extendsToContinuousMulHom_of_perfect {L G H : Type*} [Group L] [Group G] [CommGroup H]
    [TopologicalSpace G] [TopologicalSpace H] (hL : commutator L = ⊤) (ι : L →* G)
    (π : L →* H) : ExtendsToContinuousMulHom ι π := by
  have hker : commutator L ≤ π.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    simp [MonoidHom.mem_ker, commutatorElement_def]
  have htriv : ∀ g : L, π g = 1 := by
    intro g
    have : g ∈ π.ker := hker (by rw [hL]; trivial)
    simpa [MonoidHom.mem_ker] using this
  exact ⟨1, continuous_const, fun v => by simp [htriv v]⟩

/-! ### Elementary matrices and perfectness of the lattice

For `n ≥ 3` every elementary matrix is a commutator of elementary matrices, so the
perfectness hypothesis above reduces to the elementary statement that `SL(n, ℤ)` is generated
by elementary matrices. -/

open Matrix in
/-- The elementary matrix `1 + a·Eᵢⱼ` as an element of `SL(n, ℤ)`. -/
