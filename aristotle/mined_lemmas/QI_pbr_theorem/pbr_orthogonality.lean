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

theorem pbr_orthogonality (i j : Fin 2) : cinner (pbrVec i j) (prep i j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [cinner, pbrVec, prep, qubit, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

/-! ## The ontological conclusion -/

/-- **Pusey–Barrett–Rudolph theorem.**

Setting.  `Λ` is the space of ontic states.  Two quantum preparations `i : Fin 2`
(think of `|0⟩` and `|+⟩`) give rise to probability distributions `μ i` on `Λ`.
The four-outcome measurement of `pbrVec` performed on two independently prepared
systems is described by response functions `ξ k : Λ × Λ → ℝ≥0∞`, `k : Fin 2 × Fin 2`,
which sum to `1` at every ontic state (`hnorm`).  *Preparation independence*: the
joint ontic state of the two systems is distributed as the product measure
`(μ i).prod (μ j)`.  By `pbr_orthogonality` the quantum prediction for outcome
`(i,j)` on preparation `(i,j)` is `0`, which is hypothesis `hborn`.

Conclusion (the "ψ-ontic" statement, in contrapositive form).  If `ν` is a
probability measure and `q : ℝ≥0` is such that `q • ν` is a common component of
both preparation distributions (`hoverlap`) — i.e. the model is `ψ`-epistemic
with overlap at least `q` — then `q = 0`: distinct quantum states share no
common ontic component. -/
