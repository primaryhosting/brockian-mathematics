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

lemma sum_wt_no_member (p : ℝ) (H : Finset (Finset α)) :
    ∀ B : Finset α, (∀ T ∈ H, T ⊆ B) → ((H : Set (Finset α)).Pairwise Disjoint) →
      ∑ v ∈ B.powerset, (if ∀ T ∈ H, ¬ T ⊆ v then wt p B v else 0)
        = ∏ T ∈ H, (1 - p ^ T.card) := by
  classical
  induction H using Finset.induction with
  | empty =>
      intro B _ _
      simpa using sum_wt p B
  | insert T₀ H' hT₀ ih =>
      intro B hHB hdisj
      have hT₀B : T₀ ⊆ B := hHB T₀ (Finset.mem_insert_self _ _)
      have hH'B : ∀ T ∈ H', T ⊆ B \ T₀ := by
        intro T hT
        have hTB : T ⊆ B := hHB T (Finset.mem_insert_of_mem hT)
        have hne : T ≠ T₀ := fun h => hT₀ (h ▸ hT)
        have hd : Disjoint T T₀ :=
          hdisj (by simp [hT]) (by simp) hne
        intro x hx
        exact Finset.mem_sdiff.2 ⟨hTB hx, fun hxT₀ => (Finset.disjoint_left.1 hd hx) hxT₀⟩
      have hdisj' : ((H' : Set (Finset α)).Pairwise Disjoint) := by
        intro x hx y hy hxy
        exact hdisj (by simp [hx]) (by simp [hy]) hxy
      set f : Finset α → ℝ := fun u => if ¬ T₀ ⊆ u then wt p T₀ u else 0 with hf
      set g : Finset α → ℝ :=
        fun w => if ∀ T ∈ H', ¬ T ⊆ w then wt p (B \ T₀) w else 0 with hg
      have hpoint : ∀ v ∈ B.powerset,
          (if ∀ T ∈ insert T₀ H', ¬ T ⊆ v then wt p B v else 0) = f (v ∩ T₀) * g (v \ T₀) := by
        intro v hv
        rw [Finset.mem_powerset] at hv
        have hA : T₀ ⊆ v ∩ T₀ ↔ T₀ ⊆ v := by
          constructor
          · intro h x hx; exact (Finset.mem_inter.1 (h hx)).1
          · intro h x hx; exact Finset.mem_inter.2 ⟨h hx, hx⟩
        have hB : ∀ T ∈ H', (T ⊆ v \ T₀ ↔ T ⊆ v) := by
          intro T hT
          have hne : T ≠ T₀ := fun h => hT₀ (h ▸ hT)
          have hd : Disjoint T T₀ := hdisj (by simp [hT]) (by simp) hne
          constructor
          · intro h x hx; exact (Finset.mem_sdiff.1 (h hx)).1
          · intro h x hx
            exact Finset.mem_sdiff.2 ⟨h hx, fun hxT₀ => (Finset.disjoint_left.1 hd hx) hxT₀⟩
        by_cases hc₀ : T₀ ⊆ v
        · have h1 : ¬ (∀ T ∈ insert T₀ H', ¬ T ⊆ v) := by
            intro h; exact h T₀ (Finset.mem_insert_self _ _) hc₀
          simp only [hf, hg, if_neg h1]
          rw [if_neg (by simpa [hA] using hc₀)]
          ring
        · by_cases hc1 : ∀ T ∈ H', ¬ T ⊆ v
          · have h1 : ∀ T ∈ insert T₀ H', ¬ T ⊆ v := by
              intro T hT
              rcases Finset.mem_insert.1 hT with h | h
              · exact h ▸ hc₀
              · exact hc1 T h
            have h2 : ∀ T ∈ H', ¬ T ⊆ v \ T₀ := fun T hT h => hc1 T hT ((hB T hT).1 h)
            simp only [hf, hg, if_pos h1, if_pos h2,
              if_pos (show ¬ T₀ ⊆ v ∩ T₀ from fun h => hc₀ (hA.1 h))]
            exact wt_split p hT₀B hv
          · push_neg at hc1
            obtain ⟨T, hT, hTv⟩ := hc1
            have h1 : ¬ (∀ T ∈ insert T₀ H', ¬ T ⊆ v) := by
              intro h; exact h T (Finset.mem_insert_of_mem hT) hTv
            have h2 : ¬ (∀ T ∈ H', ¬ T ⊆ v \ T₀) := by
              intro h; exact h T hT ((hB T hT).2 hTv)
            simp only [hf, hg, if_neg h1, if_neg h2]
            ring
      rw [Finset.sum_congr rfl hpoint, sum_split hT₀B f g]
      have hfirst : (∑ u ∈ T₀.powerset, f u) = 1 - p ^ T₀.card := by
        have hkey : ∀ u ∈ T₀.powerset, f u = wt p T₀ u - (if u = T₀ then wt p T₀ T₀ else 0) := by
          intro u hu
          rw [Finset.mem_powerset] at hu
          by_cases h : u = T₀
          · subst h
            simp [hf]
          · have hns : ¬ T₀ ⊆ u := fun hsub => h (Finset.Subset.antisymm hu hsub)
            simp only [hf, if_pos hns, if_neg h, sub_zero]
        rw [Finset.sum_congr rfl hkey, Finset.sum_sub_distrib, sum_wt,
          Finset.sum_ite_eq' T₀.powerset T₀ (fun _ => wt p T₀ T₀)]
        simp [Finset.mem_powerset, wt_self]
      rw [hfirst, ih (B \ T₀) hH'B hdisj', Finset.prod_insert hT₀]

/-- For a family of pairwise disjoint sets, the probability that `α_p` contains no member
is the product `∏_{T ∈ H} (1 - p ^ |T|)`. -/
