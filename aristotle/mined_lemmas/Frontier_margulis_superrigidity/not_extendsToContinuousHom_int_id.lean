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

theorem not_extendsToContinuousHom_int_id :
    ¬ ExtendsToContinuousHom (Int.castAddHom ℝ) (AddMonoidHom.id ℤ) := by
  rintro ⟨ρ, hρ, h⟩
  have hsub : Set.Subsingleton (Set.range ρ) := (isPreconnected_range hρ).subsingleton
  have h01 : ρ (0 : ℝ) = ρ (1 : ℝ) :=
    hsub (Set.mem_range_self (0 : ℝ)) (Set.mem_range_self (1 : ℝ))
  have h1 : ρ (1 : ℝ) = 1 := by simpa using h 1
  rw [map_zero, h1] at h01
  exact zero_ne_one h01

/-! ## The statement for higher-rank lattices

We now write down the statement of Margulis superrigidity in the model higher-rank case of the
lattice `SL(n, ℤ) ⊂ SL(n, ℝ)` with `n ≥ 3` (real rank `n - 1 ≥ 2`) and target `SL(m, ℝ)`.
The two hypotheses of the theorem — Zariski density and unboundedness of the image — are
spelled out directly in terms of matrix entries. -/

open Matrix in
/-- Evaluation of matrix entries as a point of affine `m × m`-space. -/
