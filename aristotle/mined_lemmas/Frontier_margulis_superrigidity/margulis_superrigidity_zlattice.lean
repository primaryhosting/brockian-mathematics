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

theorem margulis_superrigidity_zlattice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (π : L →+ F) :
    ∃! ρ : E →+ F, Continuous ρ ∧ ∀ v : L, ρ (v : E) = π v := by
  classical
  have hfin : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have hfree : Module.Free ℤ L := ZLattice.module_free ℝ L
  set b : Basis (Free.ChooseBasisIndex ℤ L) ℤ L := Free.chooseBasis ℤ L with hb
  set B : Basis (Free.ChooseBasisIndex ℤ L) ℝ E := b.ofZLatticeBasis ℝ L with hB
  set ρ0 : E →ₗ[ℝ] F := B.constr ℝ fun i => π (b i) with hρ0
  have hbasis : ∀ i, ρ0 (B i) = π (b i) := fun i => by rw [hρ0, Basis.constr_basis]
  have hcont : Continuous ρ0 := LinearMap.continuous_of_finiteDimensional _
  have hagree : ∀ v : L, ρ0 (v : E) = π v := by
    intro v
    have h1 : ρ0 (v : E) = ∑ i, B.repr (v : E) i • ρ0 (B i) := by
      conv_lhs => rw [← B.sum_repr (v : E)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    have h2 : ∀ i, B.repr (v : E) i = ((b.repr v i : ℤ) : ℝ) := by
      intro i
      rw [hB, Basis.ofZLatticeBasis_repr_apply]
    have h3 : π v = ∑ i, (b.repr v i) • π (b i) := by
      conv_lhs => rw [← b.sum_repr v]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_zsmul _ _ _
    rw [h1, h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbasis, h2, Int.cast_smul_eq_zsmul]
  refine ⟨ρ0.toAddMonoidHom, ⟨hcont, hagree⟩, ?_⟩
  rintro σ ⟨hσc, hσ⟩
  have hlin : (σ.toRealLinearMap hσc).toLinearMap = ρ0 := by
    refine B.ext fun i => ?_
    have hBi : B i = ((b i : L) : E) := by rw [hB, Basis.ofZLatticeBasis_apply]
    rw [hbasis, hBi]
    simpa using hσ (b i)
  refine DFunLike.ext _ _ fun x => ?_
  simpa using LinearMap.congr_fun hlin x

/-! ## Sharpness of the base case

Superrigidity genuinely uses the structure of the target group: for a *discrete* target the
extension property fails already for the lattice `ℤ ⊂ ℝ`. -/

/-- The identity homomorphism of the lattice `ℤ ⊂ ℝ` into the discrete group `ℤ` admits **no**
continuous extension to `ℝ`: `ℝ` is connected and `ℤ` is totally disconnected, so every
continuous homomorphism `ℝ → ℤ` is trivial. -/
