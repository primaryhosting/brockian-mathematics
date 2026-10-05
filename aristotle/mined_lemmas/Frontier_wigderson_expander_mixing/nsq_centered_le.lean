/-
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

namespace Frontier

section Mixing

variable {n : ℕ}

/-- The bilinear form `xᵀ A y` associated with a real matrix `A`. -/

lemma nsq_centered_le (hn : 0 < n) (S : Finset (Fin n)) :
    nsq (fun i => (if i ∈ S then (1:ℝ) else 0) - (S.card : ℝ) / n) ≤ (S.card : ℝ) := by
  have hns : (0:ℝ) < n := by exact_mod_cast hn
  have hexp : nsq (fun i => (if i ∈ S then (1:ℝ) else 0) - (S.card : ℝ) / n)
      = (S.card : ℝ) - (S.card : ℝ) ^ 2 / n := by
    unfold nsq
    have hpt : ∀ i : Fin n, ((if i ∈ S then (1:ℝ) else 0) - (S.card : ℝ) / n) ^ 2
        = (if i ∈ S then (1:ℝ) else 0) * (1 - 2 * ((S.card : ℝ) / n))
            + ((S.card : ℝ) / n) ^ 2 := by
      intro i
      by_cases h : i ∈ S
      · simp [h]; ring
      · simp [h]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hpt i), Finset.sum_add_distrib,
      ← Finset.sum_mul]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_mem, Finset.univ_inter, mul_one]
    field_simp
    ring
  rw [hexp]
  have : (0:ℝ) ≤ (S.card : ℝ) ^ 2 / n := by positivity
  linarith

/-- **Expander mixing lemma** (Alon–Chung; see Hoory–Linial–Wigderson).

Let `A` be the (real, symmetric) adjacency matrix of a `d`-regular graph on `n` vertices,
and suppose the quadratic form of `A` is bounded in absolute value by `lam` on the space of
vectors orthogonal to the all-ones vector (i.e. `lam` bounds the non-trivial eigenvalues in
absolute value).  Then for all vertex subsets `S`, `T`, the number of edges from `S` to `T`
(counted with the adjacency matrix) deviates from its "expected" value `d|S||T|/n` by at most
`lam * sqrt(|S||T|)`. -/
