import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma ankeny_lattice_covolume (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    ∃ (L : AddSubgroup (Fin 3 → ℝ)) (F : Set (Fin 3 → ℝ)),
      IsAddFundamentalDomain L F volume ∧
      volume F = (2 * n * q : ℝ≥0∞) ∧
      (L : Set (Fin 3 → ℝ)).Countable ∧
      (L : Set (Fin 3 → ℝ)) ⊆ ankeny_lattice n q b := by
  classical
  let L : AddSubgroup E3 := ankeny_span_lattice n q b hn hq
  let F : Set E3 := ankeny_span_fundamentalDomain n q b hn hq
  refine ⟨L, F, ?_, ?_, ?_, ?_⟩
  · simpa [L, F] using ankeny_span_isAddFundamentalDomain n q b hn hq
  · simpa [F] using ankeny_span_volume_fundamentalDomain n q b hn hq
  · -- Countability of the ℤ-span lattice.
    have : Countable (↥L) := by
      -- `L` is a `Submodule.span ℤ` of a finite `Set.range`, hence countable.
      change Countable (Submodule.span ℤ (Set.range (ankeny_span_basis n q b hn hq)))
      infer_instance
    -- Convert subtype-countability into set-countability.
    have hrange : (Set.range (fun x : (↥L) => (x : E3))) = (L : Set E3) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    simpa [hrange] using (Set.countable_range (fun x : (↥L) => (x : E3)))
  · -- Inclusion into the congruence-defined lattice is the arithmetic glue step.
    simpa [L] using ankeny_span_lattice_subset_ankeny_lattice n q b hn hq

/-- The quadratic form `Q = 2qx² + y² + nz²`. -/
