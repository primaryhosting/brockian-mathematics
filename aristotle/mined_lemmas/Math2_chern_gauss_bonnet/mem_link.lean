import Mathlib

/-!
# Gauss–Bonnet (the `n = 1` case of Chern–Gauss–Bonnet) for the 2-torus

This file contains a *smooth* instance of the Chern–Gauss–Bonnet theorem, complementing the
combinatorial theorem `Math2.chern_gauss_bonnet` in `RequestProject.Main`.

For a closed oriented surface `M` the Chern–Gauss–Bonnet theorem reads
`∫_M K dA = 2π χ(M)`.  We prove this for the closed even-dimensional manifold
`T² = ℝ²/ℤ²` equipped with an *arbitrary* conformal metric `e^{2u}(dx² + dy²)`, where `u` is
any doubly periodic potential with enough regularity.  For such a metric the Gauss curvature
is `K = -e^{-2u} Δu` and the area density is `e^{2u}`, so the total curvature is `-∫∫ Δu`,
which vanishes by periodicity — in agreement with `χ(T²) = 0`.
-/

namespace Math2.Torus

open MeasureTheory

/-- Partial derivative in the first variable. -/

lemma mem_link {v : V} {s : Finset V} :
    s ∈ K.link v ↔ v ∉ s ∧ insert v s ∈ K.faces := by
  classical
  constructor
  · intro hs
    simp only [link, Finset.mem_image, Finset.mem_filter] at hs
    obtain ⟨t, ⟨ht, hvt⟩, rfl⟩ := hs
    refine ⟨Finset.notMem_erase v t, ?_⟩
    rwa [Finset.insert_erase hvt]
  · rintro ⟨hvs, hins⟩
    simp only [link, Finset.mem_image, Finset.mem_filter]
    exact ⟨insert v s, ⟨hins, Finset.mem_insert_self v s⟩, by
      simp [Finset.erase_insert hvs]⟩

/-- The curvature at `v` computed from the link (combinatorial unit sphere) of `v`:
`K(v) = ∑_{σ ∈ link(v) ∪ {∅}} (-1)^{|σ|} / (|σ| + 1)`. -/
