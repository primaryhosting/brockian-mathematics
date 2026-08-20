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

protected theorem sum (s : Finset ι) (f : ι → Language α) (h : ∀ i ∈ s, IsRegexLang (f i)) :
    IsRegexLang (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IsRegexLang.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end IsRegexLang

