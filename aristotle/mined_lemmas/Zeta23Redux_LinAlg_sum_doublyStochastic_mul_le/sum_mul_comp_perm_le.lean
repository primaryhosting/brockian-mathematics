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

import Mathlib
/-!
# Sum Doubly Stochastic Mul Le
Category: Linalg
Target: Zeta23Redux.LinAlg.sum_doublyStochastic_mul_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset Matrix

namespace Zeta23Redux.LinAlg

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

omit [LinearOrder ι] in
/-- For a permutation matrix, the double sum `∑ i ∑ j (permMatrix σ) i j * (μ i * ν j)`
collapses to `∑ i, μ i * ν (σ i)`. -/

lemma sum_mul_comp_perm_le (σ : Equiv.Perm ι) {μ ν : ι → ℝ}
    (hμ : Antitone μ) (hν : Antitone ν) :
    ∑ i, μ i * ν (σ i) ≤ ∑ i, μ i * ν i := by
  simpa [smul_eq_mul] using
    (hμ.monovary hν).sum_smul_comp_perm_le_sum_smul (σ := σ)

/-- **Rearrangement / Birkhoff step of the von Neumann trace inequality.**
If `S` is doubly stochastic and `μ`, `ν` are antitone weight sequences, then
`∑ᵢⱼ Sᵢⱼ · μᵢ · νⱼ ≤ ∑ᵢ μᵢ · νᵢ`. -/
