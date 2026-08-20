import Mathlib

/-!
# The `p`-biased measure on subsets of a finite set

Auxiliary measure-theoretic development for `RequestProject.Main` (Kahn–Kalai):
the distribution of the random subset `α_p`, its basic properties, and a block
factorisation which expresses independence over disjoint blocks.
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

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false
namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## The Kahn–Kalai setting

We fix a finite ground set `α`.  For `p ∈ [0,1]`, `α_p` denotes the random subset of `α`
containing each point independently with probability `p`; its distribution is given by the
weights `weight p S = p ^ |S| * (1 - p) ^ (n - |S|)`.

A family `H` of subsets is `q`-*small* if it admits a cover `G` — every member of `H`
contains a member of `G` — of total cost `∑_{g ∈ G} q ^ |g| ≤ 1/2`; the *expectation
threshold* `q(F)` is the largest `q` for which `F` is `q`-small, while the *threshold*
`p_c(F)` is the `p` at which `ℙ(α_p ∈ F) = 1/2`.

### Scope of this file

* `Math2.prob_le_half_of_isSmall` proves, for an **arbitrary** family, the easy direction
  `q(F) ≤ p_c(F)`: if `H` is `q`-small then `ℙ(α_q ∈ ⟨H⟩) ≤ 1/2`.
* `Math2.kahn_kalai` combines this with the converse (Park–Pham) direction for families of
  **pairwise disjoint** sets, for which threshold and expectation threshold are within a
  factor `2`, with no logarithmic loss.
* `Math2.bonferroni_le_prob` and `Math2.half_lt_prob_of_not_isSmall_of_smallOverlap` give the
  same converse direction for arbitrary families whose pairwise overlap term is small.
* The full Park–Pham theorem, `p_c(F) = O(q(F) · log ℓ(F))` for an arbitrary `ℓ`-bounded
  family, is **not** formalised here; in that generality only the easy direction is proved.
-/

/-- The `p`-biased weight of a subset `S` of the finite ground set `α`: the probability
that the random subset `α_p` is exactly `S`. -/

lemma prob_superset (p : ℝ) (G : Finset α) :
    prob p (Finset.univ.filter (fun S => G ⊆ S)) = p ^ G.card := by
  have key : ∑ S ∈ Finset.univ.filter (fun S : Finset α => G ⊆ S), weight p S
      = ∑ t ∈ (Gᶜ : Finset α).powerset, weight p (t ∪ G) := by
    refine Finset.sum_nbij' (fun S => S \ G) (fun t => t ∪ G) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter] at hS
      simp only [Finset.mem_powerset]
      intro x hx
      simp only [Finset.mem_sdiff] at hx
      simpa using hx.2
    · intro t _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.subset_union_right
    · intro S hS
      simp only [Finset.mem_filter] at hS
      exact Finset.sdiff_union_of_subset hS.2
    · intro t ht
      simp only [Finset.mem_powerset] at ht
      show (t ∪ G) \ G = t
      rw [Finset.union_sdiff_right]
      exact Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_left.2 fun x hx hxG =>
        (Finset.mem_compl.1 (ht hx)) hxG)
    · intro S hS
      simp only [Finset.mem_filter] at hS
      rw [Finset.sdiff_union_of_subset hS.2]
  rw [prob, key]
  have hcard : ∀ t ∈ (Gᶜ : Finset α).powerset, weight p (t ∪ G)
      = p ^ G.card * (p ^ t.card * (1 - p) ^ ((Gᶜ : Finset α).card - t.card)) := by
    intro t ht
    simp only [Finset.mem_powerset] at ht
    have hdisj : Disjoint t G :=
      Finset.disjoint_left.2 fun x hx hxG => (Finset.mem_compl.1 (ht hx)) hxG
    have h1 : (t ∪ G).card = t.card + G.card := Finset.card_union_of_disjoint hdisj
    unfold weight
    rw [h1, Finset.card_compl, pow_add]
    have h2 : Fintype.card α - (t.card + G.card) = Fintype.card α - G.card - t.card := by omega
    rw [h2]
    ring
  rw [Finset.sum_congr rfl hcard, ← Finset.mul_sum, sum_pow_powerset]
  ring

/-- The probability that `α_p` misses a fixed set `T` is `(1 - p) ^ |T|`. -/
