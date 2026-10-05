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

This file formalises the Pusey–Barrett–Rudolph (PBR) theorem: in any ontological
(hidden-variable) model reproducing the quantum predictions, under the
*preparation independence* assumption, the probability distributions over ontic
states associated with two distinct (non-orthogonal) quantum preparations cannot
overlap.  Equivalently, the quantum state is *ontic* rather than *epistemic*.

Two ingredients are given.

* `QI.pbr_orthogonality` : the quantum input.  The four (unnormalised) PBR
  measurement vectors on `ℂ² ⊗ ℂ²` are pairwise orthogonal and each of them is
  orthogonal to exactly one of the four product preparations `|0⟩|0⟩`,
  `|0⟩|+⟩`, `|+⟩|0⟩`, `|+⟩|+⟩`.  Hence a quantum model predicts probability `0`
  for outcome `(i,j)` on preparation `(i,j)`.

* `QI.pbr_theorem` : the ontological conclusion.  Given an ontological model
  with response functions summing to one, preparation independence (the ontic
  state of two independently prepared systems is distributed according to the
  product measure) and the above zero predictions, any common component `q • ν`
  of the two preparation distributions must be trivial, i.e. `q = 0`.
-/

namespace QI

open MeasureTheory
open scoped ENNReal

/-! ## The quantum input: the PBR measurement -/

/-- Hermitian inner product on `ℂ⁴ = ℂ² ⊗ ℂ²`, whose index set is `Fin 2 × Fin 2`. -/

def qubit : Fin 2 → Fin 2 → ℂ := ![![1, 0], ![1, 1]]

/-- The product preparation `|ψ i⟩ ⊗ |ψ j⟩`. -/
