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

set_option grind.warning false

namespace Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The "centered indicator" of a finite set `S`: the indicator of `S` minus its mean value.
It is orthogonal to the all-ones vector. -/

lemma bilinear_centeredIndicator (hV : (Fintype.card V) ≠ 0)
    (A : Matrix V V ℝ) (d : ℝ)
    (hrow : ∀ i, ∑ j, A i j = d) (hcol : ∀ j, ∑ i, A i j = d)
    (S T : Finset V) :
    ∑ i, ∑ j, centeredIndicator S i * A i j * centeredIndicator T j
      = (∑ i ∈ S, ∑ j ∈ T, A i j)
        - d * S.card * T.card / (Fintype.card V) := by
  have hn : ((Fintype.card V : ℝ)) ≠ 0 := by exact_mod_cast hV
  -- inner sum over `j`
  have hinner : ∀ i : V, ∑ j, A i j * centeredIndicator T j
      = (∑ j ∈ T, A i j) - ((T.card : ℝ) / (Fintype.card V)) * d := by
    intro i
    simp only [centeredIndicator, mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1
    · simp [Finset.sum_ite_mem]
    · rw [← Finset.sum_mul, hrow i]; ring
  have hstep : ∑ i, ∑ j, centeredIndicator S i * A i j * centeredIndicator T j
      = ∑ i, centeredIndicator S i *
          ((∑ j ∈ T, A i j) - ((T.card : ℝ) / (Fintype.card V)) * d) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hinner i, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hstep]
  -- split off the constant part
  have hsplit : ∑ i, centeredIndicator S i *
      ((∑ j ∈ T, A i j) - ((T.card : ℝ) / (Fintype.card V)) * d)
      = (∑ i, centeredIndicator S i * (∑ j ∈ T, A i j))
        - (((T.card : ℝ) / (Fintype.card V)) * d) * (∑ i, centeredIndicator S i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit, sum_centeredIndicator hV S, mul_zero, sub_zero]
  -- total sum of the column-restricted row sums
  have htot : ∑ i, (∑ j ∈ T, A i j) = (T.card : ℝ) * d := by
    rw [Finset.sum_comm]
    simp [hcol, mul_comm]
  have : ∑ i, centeredIndicator S i * (∑ j ∈ T, A i j)
      = (∑ i ∈ S, ∑ j ∈ T, A i j)
        - ((S.card : ℝ) / (Fintype.card V)) * ((T.card : ℝ) * d) := by
    simp only [centeredIndicator, sub_mul]
    rw [Finset.sum_sub_distrib]
    congr 1
    · simp [Finset.sum_ite_mem]
    · rw [← Finset.mul_sum, htot]
  rw [this]
  field_simp

/--
**Expander mixing lemma** (Alon–Chung; see Hoory–Linial–Wigderson, *Expander graphs and their
applications*, Lemma 2.5).

Let `A` be the adjacency matrix (or any real matrix) on a finite vertex set `V` with
`n = |V| > 0`, all of whose row sums and column sums equal `d` (i.e. `A` is `d`-regular, so the
all-ones vector is an eigenvector with eigenvalue `d`).  Suppose `A` has spectral gap `lam ≥ 0`,
expressed as the bound `|xᵀ A y| ≤ lam ‖x‖ ‖y‖` for all vectors `x, y` orthogonal to the
all-ones vector (this is exactly the statement that the second largest eigenvalue in absolute
value is at most `lam`).

Then for all sets of vertices `S, T`, the number of edges between them, `e(S,T) = ∑_{i∈S,j∈T} Aᵢⱼ`,
deviates from its "expected" value `d|S||T|/n` by at most `lam √(|S||T|)`.
-/
