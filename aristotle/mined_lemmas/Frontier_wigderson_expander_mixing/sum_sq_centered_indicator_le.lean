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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- Cauchy–Schwarz in the form `|⟪f, g⟫| ≤ ‖f‖ ‖g‖` for finite sums of reals. -/

lemma sum_sq_centered_indicator_le {V : Type*} [Fintype V] (S : Finset V)
    (hn : (0 : ℝ) < Fintype.card V) :
    ∑ i, ((if i ∈ S then (1 : ℝ) else 0) - S.card / Fintype.card V) ^ 2 ≤ S.card := by
  have hexp : ∀ i : V, ((if i ∈ S then (1 : ℝ) else 0) - S.card / Fintype.card V) ^ 2
      = (if i ∈ S then (1 : ℝ) else 0)
        - 2 * (S.card / Fintype.card V) * (if i ∈ S then (1 : ℝ) else 0)
        + (S.card / Fintype.card V) ^ 2 := by
    intro i
    by_cases h : i ∈ S
    · rw [if_pos h]; ring
    · rw [if_neg h]; ring
  rw [Finset.sum_congr rfl fun i _ => hexp i]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    nsmul_eq_mul]
  have hcard : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt hn
  have h2 : 0 ≤ (S.card : ℝ) ^ 2 / Fintype.card V := by positivity
  have h3 : (Fintype.card V : ℝ) * ((S.card : ℝ) / Fintype.card V) ^ 2
      = (S.card : ℝ) ^ 2 / Fintype.card V := by field_simp
  have h4 : 2 * ((S.card : ℝ) / Fintype.card V) * ((S.card : ℝ) * 1)
      = 2 * ((S.card : ℝ) ^ 2 / Fintype.card V) := by field_simp
  rw [h3, h4]
  linarith

/-- **Expander mixing lemma** (Alon–Chung / Wigderson form).

Let `A` be a real symmetric matrix on a finite nonempty vertex set `V` (the adjacency
matrix of a `d`-regular graph), with all row sums equal to `d`, and suppose that `A`
contracts every vector orthogonal to the all-ones vector by a factor at most `lam`
(i.e. `lam` bounds the second largest eigenvalue in absolute value). Then for all
sets `S`, `T` of vertices, the number of edges between `S` and `T` (counted via `A`)
deviates from its "random graph" expectation `d |S| |T| / n` by at most
`lam * sqrt (|S| |T|)`. -/
