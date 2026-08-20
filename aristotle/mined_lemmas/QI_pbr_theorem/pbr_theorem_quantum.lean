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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/--
**Pusey–Barrett–Rudolph theorem** (the quantum state is ontic).

Setting: an ontological (hidden-variable) model with a finite space `Λ` of ontic states.
Two distinct quantum preparations, indexed by `Bool`, are represented by probability
distributions `mu false, mu true : Λ → ℝ` over `Λ` (`hmu_nonneg`, `hmu_sum`).

*Preparation independence*: when two systems are prepared independently, with
preparations `o.1` and `o.2`, the joint distribution of their ontic states is the
product `mu o.1 l₁ * mu o.2 l₂`.

The two systems are subjected to a joint measurement whose outcomes are indexed by
`Bool × Bool`; `p l₁ l₂ o` is the probability of outcome `o` given the ontic state
`(l₁, l₂)` (`hp_nonneg`, `hp_sum`).

*Antidistinguishability* (the quantum prediction realized by the PBR entangled
measurement): outcome `o` never occurs on the product preparation `o` (`hanti`).

Conclusion: the two preparations have disjoint (and nonempty) supports, i.e. no
ontic state is compatible with both quantum states — the quantum state is ontic,
not merely epistemic.
-/

theorem pbr_theorem_quantum {Λ : Type*} [Fintype Λ]
    (mu : Bool → Λ → ℝ)
    (hmu_nonneg : ∀ i l, 0 ≤ mu i l)
    (hmu_sum : ∀ i, ∑ l, mu i l = 1)
    (p : Λ → Λ → Bool × Bool → ℝ)
    (hp_nonneg : ∀ l₁ l₂ o, 0 ≤ p l₁ l₂ o)
    (hp_sum : ∀ l₁ l₂, ∑ o : Bool × Bool, p l₁ l₂ o = 1)
    (hborn : ∀ o : Bool × Bool,
      ∑ l₁, ∑ l₂, mu o.1 l₁ * mu o.2 l₂ * p l₁ l₂ o
        = Complex.normSq (inn (xiPBR o) (psiPBR o))) :
    (∀ l, mu false l = 0 ∨ mu true l = 0) ∧
      (∃ l, 0 < mu false l) ∧ (∃ l, 0 < mu true l) := by
  refine pbr_theorem mu hmu_nonneg hmu_sum p hp_nonneg hp_sum ?_
  intro o
  rw [hborn o, xiPBR_orth_psiPBR o, map_zero]

end QI

