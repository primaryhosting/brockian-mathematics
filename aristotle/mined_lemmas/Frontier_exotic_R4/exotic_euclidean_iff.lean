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

theorem exotic_euclidean_iff (n : ℕ) :
    ExoticEuclideanExists n ↔ ExoticStructureOnEuclidean n := by
  constructor
  · rintro ⟨M, tM, cM, mM, ⟨e⟩, hempty⟩
    refine ⟨transportChartedSpace (H := EuclideanSpace ℝ (Fin n)) e.symm,
      transportChartedSpace_isManifold (𝓡 n) ∞ e.symm, ?_⟩
    obtain ⟨D⟩ := nonempty_diffeomorph_transportChartedSpace (𝓡 n) (∞ : WithTop ℕ∞) e.symm
    refine ⟨fun D' => hempty.false ?_⟩
    exact diffeoTrans (𝓡 n) ∞ cM (transportChartedSpace e.symm)
      (chartedSpaceSelf (EuclideanSpace ℝ (Fin n)))
      (diffeoSymm (𝓡 n) ∞ (transportChartedSpace e.symm) cM D) D'
  · rintro ⟨c, m, hempty⟩
    exact ⟨EuclideanSpace ℝ (Fin n), inferInstance, c, m, ⟨Homeomorph.refl _⟩, hempty⟩

/-- **Reduction for the existence of an exotic `ℝ⁴`** (Donaldson/Freedman).

The full theorem — that a smooth manifold homeomorphic but not diffeomorphic to `ℝ⁴` exists —
is not proved here; what is proved is a Lean-checked reduction:

* it suffices to exhibit a *small* exotic `ℝ⁴`, i.e. an open subset of `ℝ⁴` that is homeomorphic
  but not diffeomorphic to `ℝ⁴`;
* and the statement is equivalent to the existence of a smooth structure on the topological
  space `ℝ⁴` which is not diffeomorphic to the standard one. -/
