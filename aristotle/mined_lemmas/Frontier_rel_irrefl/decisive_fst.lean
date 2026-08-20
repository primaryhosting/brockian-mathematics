/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Arrow's impossibility theorem

A *ranking* of a type `A` of alternatives is a strict total order (transitive, total on
distinct elements, asymmetric).  A *social welfare function* is a map
`F : (V → Ranking A) → Ranking A` sending each profile of individual rankings (one for each
voter `i : V`) to a social ranking.

We prove: if `V` is a finite nonempty set of voters, `A` has at least three elements, and `F`
satisfies unanimity (Pareto) and independence of irrelevant alternatives (IIA), then `F` has a
dictator.  Equivalently, no `F` satisfies unanimity, IIA and non-dictatorship
(`Frontier.arrow_impossibility`).

Mathlib does not contain Arrow's theorem, so the development is from scratch.  The proof is the
classical one: a *field expansion* lemma (semi-decisiveness over one pair implies decisiveness
over all pairs) followed by a *group contraction* lemma (a decisive coalition splits into two
parts, one of which is decisive), and then induction on the size of the coalition starting from
the grand coalition, which is decisive by unanimity.
-/

namespace Frontier

/-- A strict total order ("ranking") on the type of alternatives `A`. -/
structure Ranking (A : Type*) where
  /-- The strict preference relation. -/
  rel : A → A → Prop
  rel_trans : ∀ {x y z}, rel x y → rel y z → rel x z
  rel_total : ∀ {x y}, x ≠ y → rel x y ∨ rel y x
  rel_asymm : ∀ {x y}, rel x y → ¬ rel y x

namespace Ranking

variable {A : Type*}


lemma decisive_fst (hPar : Pareto F) (hIIA : IIA F) {S : Finset V} {p q r : A}
    (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q) (hsd : SemiDecisive F S p q) :
    Decisive F S p r := by
  classical
  intro P hP
  -- Members of `S` rank `p > q > r`; the others rank `q` first and keep their `p`/`r` order.
  set f : A → ℕ := fun z => if z = p then 0 else if z = q then 1 else if z = r then 2 else 3
    with hf
  set g : V → A → ℕ := fun i z => if z = q then 0 else
      if z = p then (if (P i).rel p r then 1 else 2) else
      if z = r then (if (P i).rel p r then 2 else 1) else 3 with hg
  set Q : V → Ranking A := fun i => if i ∈ S then mkRank f else mkRank (g i) with hQ
  have hfp : f p = 0 := by simp [hf]
  have hfq : f q = 1 := by simp [hf, Ne.symm hpq]
  have hfr : f r = 2 := by simp [hf, hrp, hrq]
  have hgq : ∀ i, g i q = 0 := by intro i; simp [hg]
  have hgp : ∀ i, g i p = if (P i).rel p r then 1 else 2 := by intro i; simp [hg, hpq]
  have hgr : ∀ i, g i r = if (P i).rel p r then 2 else 1 := by
    intro i; simp [hg, hrq, hrp]
  have hQS : ∀ i ∈ S, Q i = mkRank f := by intro i hi; simp [hQ, hi]
  have hQn : ∀ i ∉ S, Q i = mkRank (g i) := by intro i hi; simp [hQ, hi]
  -- everybody prefers `q` to `r`
  have h1 : (F Q).rel q r := by
    refine hPar Q q r fun i => ?_
    by_cases hi : i ∈ S
    · rw [hQS i hi]; exact mkRank_of_lt (by rw [hfq, hfr]; norm_num)
    · rw [hQn i hi]
      refine mkRank_of_lt ?_
      rw [hgq i, hgr i]; split <;> norm_num
  -- semi-decisiveness gives `p` over `q`
  have h2 : (F Q).rel p q := by
    refine semiDecisive_apply hIIA hsd Q ?_ ?_
    · intro i hi; rw [hQS i hi]; exact mkRank_of_lt (by rw [hfp, hfq]; norm_num)
    · intro i hi
      rw [hQn i hi]
      refine mkRank_of_lt ?_
      rw [hgq i, hgp i]; split <;> norm_num
  have h3 : (F Q).rel p r := (F Q).rel_trans h2 h1
  refine (hIIA Q P p r ?_).1 h3
  intro i
  by_cases hi : i ∈ S
  · rw [hQS i hi]
    exact iff_of_true (mkRank_of_lt (by rw [hfp, hfr]; norm_num)) (hP i hi)
  · rw [hQn i hi]
    by_cases hpr : (P i).rel p r
    · refine iff_of_true (mkRank_of_lt ?_) hpr
      rw [hgp i, hgr i, if_pos hpr, if_pos hpr]; norm_num
    · refine iff_of_false (mkRank_not_of_lt ?_) hpr
      rw [hgp i, hgr i, if_neg hpr, if_neg hpr]; norm_num

/-- Field expansion, step B: if `S` is semi-decisive for `(p, q)` then it is decisive for
`(r, q)` for every third alternative `r`. -/
