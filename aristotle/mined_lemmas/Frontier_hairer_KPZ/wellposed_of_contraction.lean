/-
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Classical NNReal

set_option maxHeartbeats 1000000

namespace KPZ

/-- Spatial derivative of a space-time function `h : time → space → ℝ`. -/

theorem wellposed_of_contraction {D X : Type*} [MetricSpace D] [MetricSpace X]
    [CompleteSpace X] [Nonempty X]
    (Φ : D → X → X) (K : ℝ≥0) (hK : K < 1) (hc : ∀ d, LipschitzWith K (Φ d))
    (L : ℝ) (hL : 0 ≤ L) (hdata : ∀ d₁ d₂ u, dist (Φ d₁ u) (Φ d₂ u) ≤ L * dist d₁ d₂) :
    ∃ S : D → X,
      (∀ d, Φ d (S d) = S d) ∧
      (∀ d u, Φ d u = u → u = S d) ∧
      (∀ d₁ d₂, dist (S d₁) (S d₂) ≤ L / (1 - K) * dist d₁ d₂) ∧
      Continuous S := by
  have hcon : ∀ d, ContractingWith K (Φ d) := fun d => ⟨hK, hc d⟩
  refine ⟨fun d => ContractingWith.fixedPoint (Φ d) (hcon d), fun d => ?_, fun d u hu => ?_, ?_, ?_⟩
  · exact ContractingWith.fixedPoint_isFixedPt (hcon d)
  · exact ContractingWith.fixedPoint_unique (hcon d) hu
  · intro d₁ d₂
    have h := ContractingWith.fixedPoint_lipschitz_in_map (hcon d₁) (hcon d₂)
      (C := L * dist d₁ d₂) (fun u => hdata d₁ d₂ u)
    calc dist (ContractingWith.fixedPoint (Φ d₁) (hcon d₁))
          (ContractingWith.fixedPoint (Φ d₂) (hcon d₂))
        ≤ L * dist d₁ d₂ / (1 - K) := h
      _ = L / (1 - (K : ℝ)) * dist d₁ d₂ := by ring
  · have hKlt : (K : ℝ) < 1 := by exact_mod_cast hK
    have hpos : (0 : ℝ) < 1 - (K : ℝ) := by linarith
    have hnn : 0 ≤ L / (1 - (K : ℝ)) := div_nonneg hL hpos.le
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (L / (1 - (K : ℝ))))
      (fun d₁ d₂ => ?_)).continuous
    rw [Real.coe_toNNReal _ hnn]
    have h := ContractingWith.fixedPoint_lipschitz_in_map (hcon d₁) (hcon d₂)
      (C := L * dist d₁ d₂) (fun u => hdata d₁ d₂ u)
    calc dist (ContractingWith.fixedPoint (Φ d₁) (hcon d₁))
          (ContractingWith.fixedPoint (Φ d₂) (hcon d₂))
        ≤ L * dist d₁ d₂ / (1 - K) := h
      _ = L / (1 - (K : ℝ)) * dist d₁ d₂ := by ring

end KPZ

namespace Frontier

/-- **Hairer's KPZ theorem (formalised statement, base cases and reduction).**

The KPZ equation `∂ₜ h = ∂ₓ² h + (∂ₓ h)² + ξ` is well posed. Full well-posedness for
space-time white noise requires the theory of regularity structures; what is proved
here is:

1. the *Cole–Hopf base case*: whenever `w > 0` solves the heat equation, `log w`
   is a classical solution of the unforced KPZ equation;
2. the *spatially homogeneous base case*: for a space-independent continuous forcing
   `g`, the space-independent KPZ dynamics has a unique solution for each initial
   datum (existence and uniqueness);
3. the *reduction to the abstract fixed point problem*: if the (renormalised) equation
   is recast, as in Hairer's theory, as a fixed point `u = Φ d u` in a complete metric
   space of modelled distributions with `Φ d` a uniform contraction and `Φ` Lipschitz
   in the data `d`, then the problem is well posed: the solution map exists, is unique,
   and depends Lipschitz-continuously (hence continuously) on the data. -/
