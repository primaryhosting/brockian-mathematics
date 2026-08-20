/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Classical
open MeasureTheory Filter Topology

namespace Math2

/-! ## The Pfaffian of the curvature (the Euler form density)

On a closed oriented Riemannian manifold `M` of even dimension `2 * n`, the Euler form is
`Pf(Ω / (2π))`, where `Ω` is the curvature two-form of the Levi-Civita connection written in a
local oriented orthonormal frame.  Expanding the Pfaffian and the wedge products in that frame,
`Pf(Ω / (2π))` is the multiple

`e(x) = 1 / ((8π)^n * n!) * ∑_{σ, τ ∈ S_{2n}} sgn σ * sgn τ *
          ∏_{i < n} R_{σ(2i) σ(2i+1) τ(2i) τ(2i+1)}(x)`

of the Riemannian volume form, where `R` denotes the components of the Riemann curvature tensor
in that frame.  We take this scalar density as the (frame-independent) definition of the
integrand of the Chern–Gauss–Bonnet theorem. -/

/-- The index `2 * i + j` of `Fin (2 * n)`, used to split `Fin (2 * n)` into `n` consecutive
pairs. -/

theorem graphCurvature_eq_sum_cliqueCounts (G : SimpleGraph V) (v : V) :
    graphCurvature G v = ∑ k ∈ Finset.range (Fintype.card V + 1),
      (-1) ^ (k + 1) *
        (((graphSimplices G).filter (fun s => v ∈ s ∧ s.card = k)).card : ℚ) / (k : ℚ) := by
  classical
  unfold graphCurvature
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun s : Finset V => s.card)
    (t := Finset.range (Fintype.card V + 1))
    (fun s _ => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.card_le_univ s)))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.filter_filter]
  have hterm : ∀ s ∈ (graphSimplices G).filter (fun s => v ∈ s ∧ s.card = k),
      (-1 : ℚ) ^ (s.card + 1) / (s.card : ℚ) = (-1) ^ (k + 1) / (k : ℚ) := by
    intro s hs
    simp only [Finset.mem_filter] at hs
    rw [hs.2.2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Discrete Gauss–Bonnet theorem** (Knill).  For every finite simple graph, the sum of the
combinatorial curvatures over all vertices equals the Euler characteristic of the clique
complex. -/
