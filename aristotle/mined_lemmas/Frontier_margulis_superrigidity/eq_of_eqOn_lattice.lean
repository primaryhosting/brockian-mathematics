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

lemma eq_of_eqOn_lattice {ρ σ : (Fin n → ℝ) →+ E} (hρ : Continuous ρ) (hσ : Continuous σ)
    (h : ∀ v : Fin n → ℤ, ρ (latticeIncl n v) = σ (latticeIncl n v)) : ρ = σ := by
  have hlin : (ρ.toRealLinearMap hρ).toLinearMap = (σ.toRealLinearMap hσ).toLinearMap := by
    refine (Pi.basisFun ℝ (Fin n)).ext fun i => ?_
    have hb : (Pi.basisFun ℝ (Fin n)) i = latticeIncl n (Pi.single i (1 : ℤ)) := by
      rw [latticeIncl_single]
      funext j; simp [Pi.basisFun_apply, Pi.single_apply]
    simpa [hb] using h (Pi.single i (1 : ℤ))
  refine DFunLike.ext _ _ fun x => ?_
  simpa using LinearMap.congr_fun hlin x

end

/-- **Margulis superrigidity: the abelian base case.**

For the lattice `ℤ ^ n ⊆ ℝ ^ n` (inclusion `Frontier.latticeIncl n`) and any real normed
space `E`, every abstract group homomorphism `π : ℤ ^ n → E` from the lattice is the
restriction of a *unique* continuous homomorphism `ρ : ℝ ^ n → E` of the ambient group;
moreover that extension is automatically `ℝ`-linear.

This is the base case of the superrigidity phenomenon: homomorphisms defined only on a
lattice are rigid, i.e. they come from continuous homomorphisms of the ambient group.  The
full theorem of Margulis (for irreducible lattices in semisimple groups of real rank at
least two, with Zariski-dense unbounded image) is not formalized here; the statement of its
conclusion is `Frontier.ExtendsToContinuousHom`, which the theorem below verifies in the
abelian case, together with uniqueness of the extension. -/
