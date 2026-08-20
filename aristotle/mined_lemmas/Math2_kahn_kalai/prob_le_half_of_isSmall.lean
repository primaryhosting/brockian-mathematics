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

theorem prob_le_half_of_isSmall {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {H : Finset (Finset α)} (h : IsSmall q H) :
    prob q (upClosure H) ≤ 1 / 2 := by
  obtain ⟨G, hcov, hcost⟩ := h
  have hsub : upClosure H ⊆ G.biUnion (fun g => Finset.univ.filter (fun S => g ⊆ S)) := by
    intro S hS
    simp only [upClosure, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨T, hT, hTS⟩ := hS
    obtain ⟨g, hg, hgT⟩ := hcov T hT
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨g, hg, hgT.trans hTS⟩
  calc prob q (upClosure H)
      ≤ prob q (G.biUnion (fun g => Finset.univ.filter (fun S => g ⊆ S))) :=
        prob_mono hq0 hq1 hsub
    _ ≤ ∑ g ∈ G, prob q (Finset.univ.filter (fun S => g ⊆ S)) :=
        sum_biUnion_le G _ _ (weight_nonneg hq0 hq1)
    _ = ∑ g ∈ G, q ^ g.card := Finset.sum_congr rfl fun g _ => prob_superset q g
    _ ≤ 1 / 2 := hcost

/-- A crude general upper bound for the threshold: if some member `T₀` of `H` satisfies
`p ^ |T₀| > 1/2`, then `α_p` lies in `⟨H⟩` with probability more than `1/2`.  In particular
the threshold of an `ℓ`-bounded nonempty family is at most `2 ^ (-1/ℓ)`. -/
