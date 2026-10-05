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

lemma curvature_eq_sum_link (v : V) :
    K.curvature v = ∑ s ∈ K.link v, (-1 : ℚ) ^ s.card / ((s.card : ℚ) + 1) := by
  classical
  have hinj : ∀ x ∈ K.faces.filter (fun s => v ∈ s), ∀ y ∈ K.faces.filter (fun s => v ∈ s),
      x.erase v = y.erase v → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_filter] at hx hy
    rw [← Finset.insert_erase hx.2, ← Finset.insert_erase hy.2, hxy]
  rw [link, Finset.sum_image hinj, SimplicialComplex.curvature]
  refine Finset.sum_congr rfl ?_
  intro t ht
  simp only [Finset.mem_filter] at ht
  obtain ⟨htf, hvt⟩ := ht
  obtain ⟨m, hm⟩ : ∃ m, t.card = m + 1 :=
    ⟨t.card - 1, (Nat.succ_pred_eq_of_pos (K.card_pos_of_mem htf)).symm⟩
  have hcard : (t.erase v).card = m := by
    rw [Finset.card_erase_of_mem hvt, hm]; rfl
  rw [hcard, hm]
  push_cast
  ring_nf

/-- Knill's form of the curvature: `K(v) = ∑_k (-1)^k V_{k-1}(v) / (k+1)`, where `V_{k-1}(v)`
is the number of `(k-1)`-dimensional simplices of the unit sphere (link) of `v`. -/
