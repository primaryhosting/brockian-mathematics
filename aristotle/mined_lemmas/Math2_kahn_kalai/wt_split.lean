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

lemma wt_split (p : ℝ) {T B : Finset α} (hTB : T ⊆ B) {v : Finset α} (hv : v ⊆ B) :
    wt p B v = wt p T (v ∩ T) * wt p (B \ T) (v \ T) := by
  have hcards : (v ∩ T).card + (v \ T).card = v.card :=
    Finset.card_inter_add_card_sdiff v T
  have h1 : (v ∩ T).card ≤ T.card := Finset.card_le_card Finset.inter_subset_right
  have h2 : (v \ T).card ≤ (B \ T).card :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff hv (le_refl T))
  have h3 : (B \ T).card = B.card - T.card := Finset.card_sdiff_of_subset hTB
  have h4 : T.card ≤ B.card := Finset.card_le_card hTB
  have h5 : v.card ≤ B.card := Finset.card_le_card hv
  unfold wt
  rw [show v.card = (v ∩ T).card + (v \ T).card from hcards.symm,
    show B.card - ((v ∩ T).card + (v \ T).card)
      = (T.card - (v ∩ T).card) + ((B \ T).card - (v \ T).card) by omega,
    pow_add, pow_add]
  ring

/-- If the members of `H` are pairwise disjoint subsets of `B`, the `B`-relative probability
that a random subset of `B` contains no member of `H` is `∏_{T ∈ H} (1 - p ^ |T|)`. -/
