import Mathlib

/-!
# Antimirov partial derivatives and finiteness of left quotients

This file develops Antimirov's partial derivatives of a regular expression, and uses them to
show that a language described by a regular expression has only finitely many left quotients.
Combined with the Myhill–Nerode theorem this gives the "regular expression → DFA" direction of
Kleene's theorem.
-/

namespace CS

open RegularExpression

variable {α : Type*}

/-- The language of a set of regular expressions: the union of the languages they describe. -/

theorem finite_range_leftQuotient_matches' (r : RegularExpression α) :
    (Set.range (Language.leftQuotient r.matches')).Finite := by
  have hbase : ({p | p ∈ r :: pdset r} : Set (RegularExpression α)).Finite :=
    (r :: pdset r).finite_toSet
  have hsub : Set.range (Language.leftQuotient r.matches') ⊆
      langSet '' {S | S ⊆ {p | p ∈ r :: pdset r}} := by
    rintro L ⟨w, rfl⟩
    refine ⟨{p | p ∈ pderivs [r] w}, ?_, ?_⟩
    · intro p hp
      exact pderivs_subset r w (by simp) p hp
    · have h1 : langList [r] = r.matches' := by
        ext x; simp
      rw [show langSet {p | p ∈ pderivs [r] w} = langList (pderivs [r] w) from rfl,
        langList_pderivs, h1]
  exact Set.Finite.subset (Set.Finite.image _ hbase.finite_subsets) hsub

end DecidableEq

/-- **Kleene, one direction**: a language described by a regular expression is regular. -/
