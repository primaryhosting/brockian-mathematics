/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Metric Filter Topology

/-- A parameterization `K : Θ → P` of a torus is *invariant* for the dynamics `F : P → P`
with internal (rigid rotation) dynamics `R : Θ → Θ` if it conjugates `R` to `F`:
`F (K θ) = K (R θ)` for all `θ`.  This is the standard "parameterization method"
formulation of an invariant torus carrying quasi-periodic motion with rotation `R`. -/

theorem kam_theorem {Θ P X : Type*} [MetricSpace X] [CompleteSpace X]
    (F : ℝ → P → P) (R : Θ → Θ) (emb : X → Θ → P) (T : ℝ → X → X)
    (hsol : ∀ ε u, T ε u = u → IsInvariantTorus (F ε) R (emb u))
    (L : NNReal) (hL : L < 1) (hlip : ∀ ε, LipschitzWith L (T ε))
    (u₀ : X) (h₀ : T 0 u₀ = u₀)
    (c : ℝ) (hc : ∀ ε, dist (T ε u₀) u₀ ≤ c * |ε|) (ε : ℝ) :
    ∃ u : X, IsInvariantTorus (F ε) R (emb u) ∧ T ε u = u ∧
      dist u u₀ ≤ c * |ε| / (1 - L) ∧ (∀ v, T ε v = v → v = u) ∧ (ε = 0 → u = u₀) := by
  haveI : Nonempty X := ⟨u₀⟩
  have hcon : ∀ δ : ℝ, ContractingWith L (T δ) := fun δ => ⟨hL, hlip δ⟩
  refine ⟨ContractingWith.fixedPoint (T ε) (hcon ε), ?_, ?_, ?_, ?_, ?_⟩
  · exact hsol ε _ (hcon ε).fixedPoint_isFixedPt
  · exact (hcon ε).fixedPoint_isFixedPt
  · have h1 := (hcon ε).dist_fixedPoint_le u₀
    rw [dist_comm]
    refine h1.trans ?_
    have h2 : dist u₀ (T ε u₀) ≤ c * |ε| := by rw [dist_comm]; exact hc ε
    have h3 : (0:ℝ) < 1 - L := (hcon ε).one_sub_K_pos
    gcongr
  · exact fun v hv => (hcon ε).fixedPoint_unique hv
  · rintro rfl
    exact ((hcon 0).fixedPoint_unique h₀).symm

/-! ### Base case: the unperturbed integrable system is foliated by invariant tori -/

/-- **Base case of KAM.**  For the integrable system `(p, q) ↦ (p, q + ω p)` on the phase space
`ℝⁿ × 𝕋ⁿ` (the time-one map of an integrable Hamiltonian flow with frequency map `ω`), every
torus `{p₀} × 𝕋ⁿ` is invariant and carries the rigid rotation by the frequency vector `ω p₀`. -/
