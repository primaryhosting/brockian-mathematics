import Mathlib

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

/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Finset

/-! ## The quantum ingredients

We work with two qubits, i.e. with `ℂ⁴` indexed by `Fin 4`, where the index `2*a + b`
stands for the product basis vector `|a⟩ ⊗ |b⟩`.
-/

/-- The inner product on `ℂ⁴` (conjugate-linear in the first argument). -/

theorem born_zero (i : Fin 4) : ip (xi i) (phi (pa i) (pb i)) = 0 := by
  fin_cases i <;> simp [ip, xi, phi, pa, pb, Fin.sum_univ_four]

/-! ## Ontological models with preparation independence -/

/-- An ontological model for the two preparations `|0⟩` and `|+⟩` of a qubit, together
with a response function for the PBR measurement on two independently prepared systems.

* `mu a` is the probability distribution over ontic states `Λ` prepared by `|ψ_a⟩`;
* `P l₁ l₂` is the probability distribution over the four measurement outcomes when the
  joint ontic state of the two systems is `(l₁, l₂)`;
* `born` says the model reproduces the quantum predictions, where **preparation
  independence** is encoded in the product measure `mu a l₁ * mu b l₂`. -/
structure OntologicalModel (Λ : Type) [Fintype Λ] where
  mu : Fin 2 → Λ → ℝ
  mu_nonneg : ∀ a l, 0 ≤ mu a l
  mu_sum : ∀ a, ∑ l, mu a l = 1
  P : Λ → Λ → Fin 4 → ℝ
  P_nonneg : ∀ l₁ l₂ i, 0 ≤ P l₁ l₂ i
  P_sum : ∀ l₁ l₂, ∑ i, P l₁ l₂ i = 1
  born : ∀ a b i, ∑ l₁, ∑ l₂, mu a l₁ * mu b l₂ * P l₁ l₂ i =
    Complex.normSq (ip (xi i) (phi a b))

variable {Λ : Type} [Fintype Λ]

/-- If an outcome has average probability zero for a product preparation, then it has
probability zero at every pair of ontic states in the product of the supports. -/
