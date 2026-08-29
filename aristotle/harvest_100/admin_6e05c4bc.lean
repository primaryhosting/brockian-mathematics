import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix Kronecker

namespace Frontier

variable {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n]

/-- The reduced state ("partial trace") of a bipartite density matrix on the `m`-factor
(Alice's system), obtained by tracing out the `n`-factor (Bob's system). -/
noncomputable def ptraceB (ρ : Matrix (m × n) (m × n) ℂ) : Matrix m m ℂ :=
  fun i j => ∑ k, ρ (i, k) (j, k)

/-- A local operation on Bob's half of the system: the Kraus operator `K` acting on the second
tensor factor only, i.e. `1 ⊗ K`. -/
noncomputable def localB (K : Matrix n n ℂ) : Matrix (m × n) (m × n) ℂ :=
  (1 : Matrix m m ℂ) ⊗ₖ K

/-- The action of a quantum channel on Bob's half, given in Kraus form by the family `K`. -/
noncomputable def applyB (K : ι → Matrix n n ℂ) (ρ : Matrix (m × n) (m × n) ℂ) :
    Matrix (m × n) (m × n) ℂ :=
  ∑ a, localB (K a) * ρ * (localB (K a))ᴴ

omit [DecidableEq m] [DecidableEq n] in
/-- Reordering of a quadruple iterated sum. -/
private lemma sum_reorder (T : n → ι → n → n → ℂ) :
    ∑ k, ∑ a, ∑ b, ∑ d, T k a b d = ∑ b, ∑ d, ∑ a, ∑ k, T k a b d := by
  rw [show (∑ k, ∑ a, ∑ b, ∑ d, T k a b d)
        = ∑ p : n × ι × n × n, T p.1 p.2.1 p.2.2.1 p.2.2.2 from by simp [Fintype.sum_prod_type],
      show (∑ b, ∑ d, ∑ a, ∑ k, T k a b d)
        = ∑ q : n × n × ι × n, T q.2.2.2 q.2.2.1 q.1 q.2.1 from by simp [Fintype.sum_prod_type]]
  exact Fintype.sum_equiv
    ⟨fun p => (p.2.2.1, p.2.2.2, p.2.1, p.1), fun q => (q.2.2.2, q.2.2.1, q.1, q.2.1),
      by rintro ⟨k, a, b, d⟩; rfl, by rintro ⟨b, d, a, k⟩; rfl⟩ _ _ (fun _ => rfl)

omit [DecidableEq n] in
/-- Entrywise form of a local operation conjugating a bipartite matrix. -/
private lemma localB_conj_apply (ρ : Matrix (m × n) (m × n) ℂ) (K : Matrix n n ℂ) (i j : m)
    (k : n) :
    (localB K * ρ * (localB K)ᴴ : Matrix (m × n) (m × n) ℂ) (i, k) (j, k)
      = ∑ b, ∑ d, K k b * ρ (i, b) (j, d) * (starRingEnd ℂ) (K k d) := by
  simp only [localB]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
    ite_mul, Finset.sum_mul, apply_ite (starRingEnd ℂ), mul_ite]
  rw [Finset.sum_comm]

/-- **No communication theorem.**

If Bob applies an arbitrary quantum channel to his half of a bipartite system — i.e. a trace
preserving family of Kraus operators `K a` acting as `1 ⊗ K a`, with `∑ a, (K a)ᴴ * (K a) = 1` —
then Alice's reduced density matrix is completely unchanged.  Since every statistic Alice can
observe is a function of her reduced state, Bob's local operation transmits no information. -/
theorem no_communication (ρ : Matrix (m × n) (m × n) ℂ) (K : ι → Matrix n n ℂ)
    (hK : ∑ a, (K a)ᴴ * (K a) = 1) :
    ptraceB (applyB K ρ) = ptraceB ρ := by
  ext i j
  have step : (ptraceB (applyB K ρ)) i j
      = ∑ b, ∑ d, ∑ a, ∑ k,
          K a k b * ρ (i, b) (j, d) * (starRingEnd ℂ) (K a k d) := by
    rw [← sum_reorder (fun k a b d => K a k b * ρ (i, b) (j, d) * (starRingEnd ℂ) (K a k d))]
    simp only [ptraceB, applyB, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun a _ => localB_conj_apply ρ (K a) i j k
  rw [step]
  have inner : ∀ b d : n,
      (∑ a, ∑ k, K a k b * ρ (i, b) (j, d) * (starRingEnd ℂ) (K a k d))
        = ρ (i, b) (j, d) * (∑ a, ((K a)ᴴ * (K a)) d b) := by
    intro b d
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_apply, RCLike.star_def]
    ring
  simp only [inner]
  have : ∀ (d b : n), (∑ a, ((K a)ᴴ * (K a)) d b) = (1 : Matrix n n ℂ) d b := by
    intro d b
    rw [← hK]
    simp [Matrix.sum_apply]
  simp only [this, ptraceB]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Matrix.one_apply]

/-- Specialization to a unitary local operation: if Bob applies a unitary `U` to his half,
Alice's reduced state is unchanged. -/
theorem no_communication_unitary (ρ : Matrix (m × n) (m × n) ℂ) (U : Matrix n n ℂ)
    (hU : Uᴴ * U = 1) :
    ptraceB (localB U * ρ * (localB U)ᴴ) = ptraceB ρ := by
  have h := no_communication (ι := Unit) ρ (fun _ => U) (by simpa using hU)
  simpa [applyB] using h

omit [DecidableEq m] in
/-- The expectation value of an observable `M` local to Alice depends on the global state only
through Alice's reduced state. -/
theorem trace_local_observable (ρ : Matrix (m × n) (m × n) ℂ) (M : Matrix m m ℂ) :
    (ρ * (M ⊗ₖ (1 : Matrix n n ℂ))).trace = (ptraceB ρ * M).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, ptraceB, Fintype.sum_prod_type, Finset.sum_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

/-- **No communication, statistical form.**  No measurement Alice performs can detect whether
Bob applied a local channel to his half of the entangled pair: every local expectation value is
unchanged. -/
theorem no_communication_expectation (ρ : Matrix (m × n) (m × n) ℂ) (K : ι → Matrix n n ℂ)
    (hK : ∑ a, (K a)ᴴ * (K a) = 1) (M : Matrix m m ℂ) :
    (applyB K ρ * (M ⊗ₖ (1 : Matrix n n ℂ))).trace = (ρ * (M ⊗ₖ (1 : Matrix n n ℂ))).trace := by
  rw [trace_local_observable, trace_local_observable, no_communication ρ K hK]

end Frontier

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

