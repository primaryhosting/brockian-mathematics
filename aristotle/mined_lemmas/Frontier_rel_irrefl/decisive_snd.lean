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


lemma decisive_snd (hPar : Pareto F) (hIIA : IIA F) {S : Finset V} {p q r : A}
    (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q) (hsd : SemiDecisive F S p q) :
    Decisive F S r q := by
  classical
  intro P hP
  -- Members of `S` rank `r > p > q`; the others rank `p` last and keep their `r`/`q` order.
  set f : A → ℕ := fun z => if z = r then 0 else if z = p then 1 else if z = q then 2 else 3
    with hf
  set g : V → A → ℕ := fun i z => if z = p then 2 else
      if z = r then (if (P i).rel r q then 0 else 1) else
      if z = q then (if (P i).rel r q then 1 else 0) else 3 with hg
  set Q : V → Ranking A := fun i => if i ∈ S then mkRank f else mkRank (g i) with hQ
  have hfr : f r = 0 := by simp [hf]
  have hfp : f p = 1 := by simp [hf, Ne.symm hrp]
  have hfq : f q = 2 := by simp [hf, Ne.symm hrq, Ne.symm hpq]
  have hgp : ∀ i, g i p = 2 := by intro i; simp [hg]
  have hgr : ∀ i, g i r = if (P i).rel r q then 0 else 1 := by intro i; simp [hg, hrp]
  have hgq : ∀ i, g i q = if (P i).rel r q then 1 else 0 := by
    intro i; simp [hg, Ne.symm hpq, Ne.symm hrq]
  have hQS : ∀ i ∈ S, Q i = mkRank f := by intro i hi; simp [hQ, hi]
  have hQn : ∀ i ∉ S, Q i = mkRank (g i) := by intro i hi; simp [hQ, hi]
  -- everybody prefers `r` to `p`
  have h1 : (F Q).rel r p := by
    refine hPar Q r p fun i => ?_
    by_cases hi : i ∈ S
    · rw [hQS i hi]; exact mkRank_of_lt (by rw [hfr, hfp]; norm_num)
    · rw [hQn i hi]
      refine mkRank_of_lt ?_
      rw [hgr i, hgp i]; split <;> norm_num
  -- semi-decisiveness gives `p` over `q`
  have h2 : (F Q).rel p q := by
    refine semiDecisive_apply hIIA hsd Q ?_ ?_
    · intro i hi; rw [hQS i hi]; exact mkRank_of_lt (by rw [hfp, hfq]; norm_num)
    · intro i hi
      rw [hQn i hi]
      refine mkRank_of_lt ?_
      rw [hgq i, hgp i]; split <;> norm_num
  have h3 : (F Q).rel r q := (F Q).rel_trans h1 h2
  refine (hIIA Q P r q ?_).1 h3
  intro i
  by_cases hi : i ∈ S
  · rw [hQS i hi]
    exact iff_of_true (mkRank_of_lt (by rw [hfr, hfq]; norm_num)) (hP i hi)
  · rw [hQn i hi]
    by_cases hrq' : (P i).rel r q
    · refine iff_of_true (mkRank_of_lt ?_) hrq'
      rw [hgr i, hgq i, if_pos hrq', if_pos hrq']; norm_num
    · refine iff_of_false (mkRank_not_of_lt ?_) hrq'
      rw [hgr i, hgq i, if_neg hrq', if_neg hrq']; norm_num

/-- Field expansion lemma: semi-decisiveness over a single pair implies decisiveness over
all pairs. -/
