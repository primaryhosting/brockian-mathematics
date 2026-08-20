import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

lemma exists_contDiff_approx_real {K : Set E} (hK : IsCompact K) (φ : E → ℝ)
    (hφ : ContinuousOn φ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : E → ℝ, ContDiff ℝ 1 G ∧ ∀ x ∈ K, |G x - φ x| < ε := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  set fK : C(K, ℝ) := ⟨K.restrict φ, hφ.restrict⟩ with hfK
  set A : Subalgebra ℝ C(K, ℝ) :=
  { carrier := {g : C(K, ℝ) | ∃ G : E → ℝ, ContDiff ℝ 1 G ∧ ∀ x : K, g x = G x}
    mul_mem' := by
      rintro g h ⟨G, hG, hGg⟩ ⟨H, hH, hHh⟩
      exact ⟨fun v => G v * H v, hG.mul hH, fun x => by simp [hGg x, hHh x]⟩
    add_mem' := by
      rintro g h ⟨G, hG, hGg⟩ ⟨H, hH, hHh⟩
      exact ⟨fun v => G v + H v, hG.add hH, fun x => by simp [hGg x, hHh x]⟩
    zero_mem' := ⟨fun _ => 0, contDiff_const, fun _ => rfl⟩
    one_mem' := ⟨fun _ => 1, contDiff_const, fun _ => rfl⟩
    algebraMap_mem' := fun c => ⟨fun _ => c, contDiff_const, fun _ => rfl⟩ } with hA
  have hsep : A.SeparatesPoints := by
    rintro x y hxy
    have hne : (x : E) - (y : E) ≠ 0 := sub_ne_zero.mpr (fun h => hxy (Subtype.ext h))
    let g : C(K, ℝ) := ⟨fun z : K => ⟪(x : E) - (y : E), (z : E)⟫,
      continuous_const.inner continuous_subtype_val⟩
    have hgA : g ∈ A := ⟨fun v => ⟪(x : E) - (y : E), v⟫,
      (innerSL ℝ ((x : E) - (y : E))).contDiff, fun _ => rfl⟩
    refine ⟨⇑g, ⟨g, hgA, rfl⟩, ?_⟩
    intro h
    apply hne
    have h2 : ⟪(x : E) - (y : E), (x : E) - (y : E)⟫ = 0 := by
      rw [inner_sub_right]
      have hxy' : ⟪(x : E) - (y : E), (x : E)⟫ = ⟪(x : E) - (y : E), (y : E)⟫ := h
      linarith
    exact inner_self_eq_zero.mp h2
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hmem : fK ∈ closure (A : Set C(K, ℝ)) := by
    have hmem' : fK ∈ A.topologicalClosure := by rw [htop]; trivial
    exact hmem'
  obtain ⟨g, hgA, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  obtain ⟨G, hG, hGg⟩ := hgA
  refine ⟨G, hG, fun x hx => ?_⟩
  have h1 : dist (fK ⟨x, hx⟩) (g ⟨x, hx⟩) ≤ dist fK g := ContinuousMap.dist_apply_le_dist _
  rw [Real.dist_eq] at h1
  have h2 : g ⟨x, hx⟩ = G x := hGg ⟨x, hx⟩
  have h3 : fK ⟨x, hx⟩ = φ x := rfl
  rw [h2, h3] at h1
  rw [abs_sub_comm]
  linarith

/-- Vector valued version of `exists_contDiff_approx_real`. -/
