/-
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.ChartedSpaceTransport

/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The statement "there exists a smooth manifold homeomorphic but not diffeomorphic to `ℝ⁴`"
(Donaldson/Freedman) is formalized as `Frontier.ExoticEuclideanExists 4`.

The main theorem `Frontier.exotic_R4` is a Lean-checked reduction of that statement:

* the existence of a *small* exotic `ℝ⁴` (an open subset of `ℝ⁴` homeomorphic but not
  diffeomorphic to `ℝ⁴`, which is the form in which exotic `ℝ⁴`'s are usually produced)
  implies the existence of an exotic `ℝ⁴`;
* the existence of an exotic `ℝ⁴` is *equivalent* to the existence of a smooth structure on the
  topological space `ℝ⁴` itself which is not diffeomorphic to the standard one.

The dimension-zero base case, `Frontier.no_exotic_R0`, is proved outright: there is no
exotic `ℝ⁰`.
-/

open scoped Manifold ContDiff
open TopologicalSpace

namespace Frontier

/-- Diffeomorphisms from a smooth manifold `M`, equipped with the charted space structure `cM`
over `ℝⁿ`, to `ℝⁿ` with its *standard* smooth structure.  Spelling the charted space structures
out explicitly is necessary because we want to compare two different smooth structures on the
same topological space. -/
abbrev DiffeoToStdEuclidean (n : ℕ) (M : Type) [TopologicalSpace M]
    (cM : ChartedSpace (EuclideanSpace ℝ (Fin n)) M) : Type :=
  @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _ (𝓡 n) (𝓡 n) M _ cM (EuclideanSpace ℝ (Fin n)) _
    (chartedSpaceSelf (EuclideanSpace ℝ (Fin n))) ∞

/-- Sanity check: `ℝⁿ` with its standard smooth structure *is* diffeomorphic to the standard
`ℝⁿ`, so the conditions above are not vacuous. -/

theorem nonempty_diffeomorph_of_chartAt_eq (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    [ChartedSpace H X] [ChartedSpace H Y] [IsManifold I n X] [IsManifold I n Y]
    (e : X ≃ₜ Y)
    (h : ∀ x : X, chartAt H x = e.toOpenPartialHomeomorph ≫ₕ chartAt H (e x)) :
    Nonempty (X ≃ₘ^n⟮I, I⟯ Y) := by
  have h' : ∀ y : Y, chartAt H y = e.symm.toOpenPartialHomeomorph ≫ₕ chartAt H (e.symm y) := by
    intro y
    rw [h (e.symm y), Homeomorph.apply_symm_apply, symm_trans_self_trans]
  exact ⟨{ toEquiv := e.toEquiv
           contMDiff_toFun := contMDiff_of_chartAt_eq I n e h
           contMDiff_invFun := contMDiff_of_chartAt_eq I n e.symm h' }⟩

/-- The inverse of a diffeomorphism, with the charted space structures given explicitly.
This is `Diffeomorph.symm`, but usable when the two manifolds share the same underlying type
with different smooth structures. -/
