/-
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment because Lean 4 requires every
-- `import` command to precede any module docstring; the identical header is
-- repeated as the module docstring immediately after the imports.)

import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Kronecker
open scoped Matrix

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

namespace Frontier

/-- The partial trace over the first ("Alice") tensor factor of a bipartite system
with Hilbert space `ℂ^ιA ⊗ ℂ^ιB`: states are matrices indexed by `ιA × ιB`, and
`ptraceLeft ρ` is the reduced state seen by Bob. -/
noncomputable def ptraceLeft {ιA ιB : Type*} [Fintype ιA]
    (rho : Matrix (ιA × ιB) (ιA × ιB) ℂ) : Matrix ιB ιB ℂ :=
  Matrix.of fun b b' => ∑ a : ιA, rho (a, b) (a, b')

@[simp] lemma ptraceLeft_apply {ιA ιB : Type*} [Fintype ιA]
    (rho : Matrix (ιA × ιB) (ιA × ιB) ℂ) (b b' : ιB) :
    ptraceLeft rho b b' = ∑ a : ιA, rho (a, b) (a, b') := rfl

/-- Entrywise formula for conjugating a bipartite state by a local operator `K ⊗ 1`
acting on Alice's factor only. -/
lemma local_conj_apply {ιA ιB : Type*} [Fintype ιA] [Fintype ιB] [DecidableEq ιB]
    (K : Matrix ιA ιA ℂ) (rho : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (a a' : ιA) (b b' : ιB) :
    ((K ⊗ₖ (1 : Matrix ιB ιB ℂ)) * rho * (K ⊗ₖ (1 : Matrix ιB ιB ℂ))ᴴ) (a, b) (a', b')
      = ∑ c : ιA, ∑ e : ιA, K a c * rho (c, b) (e, b') * (starRingEnd ℂ) (K a' e) := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ← Finset.univ_product_univ, Finset.sum_product,
    mul_ite, ite_mul, mul_zero, zero_mul, mul_one, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, apply_ite (star : ℂ → ℂ), star_zero, starRingEnd_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The core computation: summing the Kraus terms and tracing out Alice's factor
collapses, thanks to the completeness relation `∑ i, (K i)ᴴ * (K i) = 1`, to the
partial trace of the original state. -/
lemma sum_kraus_ptrace_entry {ιA ιB ι : Type*} [Fintype ιA] [Fintype ιB] [Fintype ι]
    [DecidableEq ιA] (rho : Matrix (ιA × ιB) (ιA × ιB) ℂ) (K : ι → Matrix ιA ιA ℂ)
    (b b' : ιB) (hK : ∑ i : ι, (K i)ᴴ * (K i) = 1) :
    ∑ i : ι, ∑ a : ιA, ∑ c : ιA, ∑ e : ιA,
        K i a c * rho (c, b) (e, b') * (starRingEnd ℂ) (K i a e)
      = ∑ a : ιA, rho (a, b) (a, b') := by
  classical
  have h1 : ∀ i : ι, ∑ a : ιA, ∑ c : ιA, ∑ e : ιA,
      K i a c * rho (c, b) (e, b') * (starRingEnd ℂ) (K i a e)
      = ∑ c : ιA, ∑ e : ιA, rho (c, b) (e, b') * ((K i)ᴴ * (K i)) e c := by
    intro i
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.conjTranspose_apply, starRingEnd_apply]
    ring
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm, Finset.sum_eq_single c]
  · rw [← Finset.mul_sum, ← Matrix.sum_apply, hK]
    simp
  · intro e _ he
    rw [← Finset.mul_sum, ← Matrix.sum_apply, hK]
    simp [he]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- **No-communication theorem** (finite-dimensional base case).

Alice and Bob share a bipartite state `ρ` on `ℂ^ιA ⊗ ℂ^ιB`, which may be arbitrarily
entangled. Alice performs an arbitrary local quantum operation on her half: a channel
given in Kraus form by operators `K i` acting on her factor only, i.e. as
`K i ⊗ 1`, subject to the trace-preservation (completeness) relation
`∑ i, (K i)ᴴ * (K i) = 1`.

Then Bob's reduced state — the partial trace over Alice's factor — is completely
unchanged. Since every statistic available to Bob is a function of his reduced state,
local operations on one half of an entangled pair cannot transmit information. -/
theorem no_communication {ιA ιB ι : Type*} [Fintype ιA] [Fintype ιB] [Fintype ι]
    [DecidableEq ιA] [DecidableEq ιB]
    (rho : Matrix (ιA × ιB) (ιA × ιB) ℂ) (K : ι → Matrix ιA ιA ℂ)
    (hK : ∑ i : ι, (K i)ᴴ * (K i) = 1) :
    ∑ i : ι, ptraceLeft ((K i ⊗ₖ (1 : Matrix ιB ιB ℂ)) * rho
        * (K i ⊗ₖ (1 : Matrix ιB ιB ℂ))ᴴ) = ptraceLeft rho := by
  classical
  ext b b'
  rw [Matrix.sum_apply]
  simp only [ptraceLeft_apply, local_conj_apply]
  exact sum_kraus_ptrace_entry rho K b b' hK

/-- Consequence: no measurement statistic of Bob's changes. For any observable `M`
on Bob's factor, the expectation value `tr(ρ_B M)` computed from Bob's reduced state
is the same before and after Alice's local operation. -/
theorem no_communication_expectation {ιA ιB ι : Type*} [Fintype ιA] [Fintype ιB]
    [Fintype ι] [DecidableEq ιA] [DecidableEq ιB]
    (rho : Matrix (ιA × ιB) (ιA × ιB) ℂ) (K : ι → Matrix ιA ιA ℂ)
    (hK : ∑ i : ι, (K i)ᴴ * (K i) = 1) (M : Matrix ιB ιB ℂ) :
    ∑ i : ι, Matrix.trace (ptraceLeft ((K i ⊗ₖ (1 : Matrix ιB ιB ℂ)) * rho
        * (K i ⊗ₖ (1 : Matrix ιB ιB ℂ))ᴴ) * M)
      = Matrix.trace (ptraceLeft rho * M) := by
  classical
  rw [← Matrix.trace_sum, ← Finset.sum_mul, no_communication rho K hK]

end Frontier

