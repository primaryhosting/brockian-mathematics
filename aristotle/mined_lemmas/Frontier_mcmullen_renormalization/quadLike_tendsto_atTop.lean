/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Set Metric

/-- A **quadratic-like map** in the sense of Douady–Hubbard: a holomorphic map
`f : U → V` between bounded connected open subsets of `ℂ` with `closure U ⊆ V`,
which is a branched covering of degree two (every fibre over `V` is a non-empty set of
at most two points, and some fibre has exactly two points). -/
structure QuadraticLike where
  /-- the small domain -/
  U : Set ℂ
  /-- the large domain -/
  V : Set ℂ
  /-- the map -/
  f : ℂ → ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isPreconnected_U : IsPreconnected U
  isPreconnected_V : IsPreconnected V
  isBounded_V : Bornology.IsBounded V
  closure_U_subset_V : closure U ⊆ V
  analyticOn : AnalyticOnNhd ℂ f U
  mapsTo : MapsTo f U V
  /-- every fibre over `V` is a pair of points (possibly a doubled point) -/
  fiber_pair : ∀ w ∈ V, ∃ z₁ z₂, U ∩ f ⁻¹' {w} = {z₁, z₂}
  /-- the degree is exactly two -/
  degree_two : ∃ w ∈ V, ∃ z₁ ∈ U, ∃ z₂ ∈ U, z₁ ≠ z₂ ∧ f z₁ = w ∧ f z₂ = w

/-- The filled Julia set of a quadratic-like map: the points whose whole forward orbit
stays in `U`. -/

theorem quadLike_tendsto_atTop (hR : 1 + ‖c‖ < R) {z : ℂ} (hz : z ∉ (quadLike c R hR).K) :
    Filter.Tendsto (fun n : ℕ => ‖(quadMap c)^[n] z‖) Filter.atTop Filter.atTop := by
  have hδ := quadMap_escape_pos hR
  rw [quadLike_K_eq hR] at hz
  simp only [mem_setOf_eq, not_forall, not_le] at hz
  obtain ⟨n, hn⟩ := hz
  rw [Filter.tendsto_atTop_atTop]
  intro M
  obtain ⟨k, hk⟩ := exists_nat_gt ((M - ‖(quadMap c)^[n] z‖) / (R * (R - 1) - ‖c‖))
  refine ⟨n + k, fun m hm => ?_⟩
  have hsplit : (quadMap c)^[m] z = (quadMap c)^[m - n] ((quadMap c)^[n] z) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  have hge := norm_iterate_escape hR hn.le (m - n)
  rw [← hsplit] at hge
  have hkm : (k : ℝ) ≤ (m - n : ℕ) := by
    have : k ≤ m - n := by omega
    exact_mod_cast this
  have hMk : M - ‖(quadMap c)^[n] z‖ < k * (R * (R - 1) - ‖c‖) := by
    rw [div_lt_iff₀ hδ] at hk
    exact hk
  nlinarith

end Quadratic

/-- **McMullen renormalization, base case.**

For every quadratic polynomial `z ↦ z ^ 2 + c` and every radius `R > 1 + ‖c‖`:

* the restriction of `z ↦ z ^ 2 + c` to `quadU c R` is a quadratic-like map onto `ball 0 R`
  (this is the map `quadLike c R hR`);
* its filled Julia set is exactly the classical filled Julia set of the polynomial, i.e. the
  set of points with bounded forward orbit: the quadratic-like dynamics captures the whole
  bounded dynamics of `z ↦ z ^ 2 + c`;
* that filled Julia set is a non-empty compact forward-invariant set, and every point outside
  it has an orbit tending to infinity;
* `Q` admits the (trivial) renormalization of period one, and every renormalization `Q'` of
  any period `p` has its small filled Julia set contained in the big one and invariant under
  the renormalized map `Q'.f = Q.f^[p]`.
-/
