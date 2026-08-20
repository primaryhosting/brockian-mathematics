import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Complex Finset

/-! ## The two-qubit vectors used in the PBR argument -/

/-- The normalisation constant `1/√2`. -/

theorem born_example : bornProb 0 0 1 = 1 / 4 := by
  simp [bornProb, xi, prep, tens, ket0, ket1, ketP, ketM, expand, Complex.normSq_apply]
  pbr_calc

end Computation

/-! ## Ontological models with preparation independence -/

/-- An ontological (hidden variable) model for the two preparations `|0⟩` and `|+⟩`,
satisfying the PBR preparation independence assumption: the ontic state of two
independently prepared systems is a pair `(λ₁, λ₂)` distributed according to the
product of the individual distributions. -/
structure OnticModel (Λ : Type) [Fintype Λ] where
  /-- `mu a` is the probability distribution over ontic states of preparation `prep a`. -/
  mu : Fin 2 → Λ → ℝ
  mu_nonneg : ∀ a l, 0 ≤ mu a l
  mu_sum : ∀ a, ∑ l, mu a l = 1
  /-- `resp i (l₁, l₂)` is the probability that the PBR measurement returns outcome `i`
  when the joint ontic state is `(l₁, l₂)`. -/
  resp : Fin 4 → Λ × Λ → ℝ
  resp_nonneg : ∀ i p, 0 ≤ resp i p
  resp_sum : ∀ p, ∑ i, resp i p = 1
  /-- The model reproduces the quantum (Born rule) statistics, with preparation
  independence built into the product form of the joint distribution. -/
  born : ∀ (i : Fin 4) (a b : Fin 2),
    ∑ p : Λ × Λ, mu a p.1 * mu b p.2 * resp i p = bornProb i a b

/-- The hypotheses of `OnticModel` are consistent: quantum theory itself provides
such a model, in which the ontic state simply *is* the quantum state.  (Of course
this model has disjoint supports, in accordance with `pbr_theorem`.) -/
