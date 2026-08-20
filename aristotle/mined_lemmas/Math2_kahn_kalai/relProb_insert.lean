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

lemma relProb_insert (p : ℝ) {x : α} {B : Finset α} (hx : x ∉ B) (P : Finset α → Prop) :
    relProb p (insert x B) P
      = (1 - p) * relProb p B P + p * relProb p B (fun v => P (insert x v)) := by
  have hdisj : Disjoint B.powerset (B.powerset.image (insert x)) := by
    refine Finset.disjoint_left.2 ?_
    intro u hu hu2
    simp only [Finset.mem_powerset] at hu
    simp only [Finset.mem_image, Finset.mem_powerset] at hu2
    obtain ⟨v, _, rfl⟩ := hu2
    exact hx (hu (Finset.mem_insert_self x v))
  have hinj : ∀ v ∈ B.powerset, ∀ v' ∈ B.powerset, insert x v = insert x v' → v = v' := by
    intro v hv v' hv' hvv
    rw [Finset.mem_powerset] at hv hv'
    have h1 : (insert x v).erase x = v := Finset.erase_insert (fun hxv => hx (hv hxv))
    have h2 : (insert x v').erase x = v' := Finset.erase_insert (fun hxv => hx (hv' hxv))
    rw [← h1, ← h2, hvv]
  have hw0 : ∀ u ∈ B.powerset, wt p (insert x B) u = (1 - p) * wt p B u := by
    intro u hu
    rw [Finset.mem_powerset] at hu
    have hcard : (insert x B).card = B.card + 1 := Finset.card_insert_of_notMem hx
    have hle : u.card ≤ B.card := Finset.card_le_card hu
    unfold wt
    rw [hcard, show B.card + 1 - u.card = (B.card - u.card) + 1 by omega, pow_succ]
    ring
  have hw1 : ∀ v ∈ B.powerset, wt p (insert x B) (insert x v) = p * wt p B v := by
    intro v hv
    rw [Finset.mem_powerset] at hv
    have hxv : x ∉ v := fun hxv => hx (hv hxv)
    have hcard : (insert x B).card = B.card + 1 := Finset.card_insert_of_notMem hx
    have hcard' : (insert x v).card = v.card + 1 := Finset.card_insert_of_notMem hxv
    have hle : v.card ≤ B.card := Finset.card_le_card hv
    unfold wt
    rw [hcard, hcard', show B.card + 1 - (v.card + 1) = B.card - v.card by omega, pow_succ]
    ring
  rw [relProb, Finset.powerset_insert, Finset.sum_union hdisj,
    Finset.sum_image hinj]
  have e0 : ∑ u ∈ B.powerset, (if P u then wt p (insert x B) u else 0)
      = (1 - p) * relProb p B P := by
    rw [relProb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    by_cases hc : P u
    · rw [if_pos hc, if_pos hc, hw0 u hu]
    · rw [if_neg hc, if_neg hc, mul_zero]
  have e1 : ∑ v ∈ B.powerset, (if P (insert x v) then wt p (insert x B) (insert x v) else 0)
      = p * relProb p B (fun v => P (insert x v)) := by
    rw [relProb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    by_cases hc : P (insert x v)
    · rw [if_pos hc, if_pos hc, hw1 v hv]
    · rw [if_neg hc, if_neg hc, mul_zero]
  rw [e0, e1]

omit [Fintype α] in
/-- For an up-closed predicate, adding a point can only help. -/
