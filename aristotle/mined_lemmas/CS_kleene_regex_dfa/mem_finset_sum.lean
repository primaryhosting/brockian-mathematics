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

theorem mem_finset_sum (s : Finset ι) (f : ι → Language α) (w : List α) :
    w ∈ ∑ i ∈ s, f i ↔ ∃ i ∈ s, w ∈ f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Language.mem_add, ih]
    simp

namespace DFAPath

variable (M : DFA α σ)

/-- `pathLang M S i j` is the set of words taking state `i` to state `j` in `M`, all of whose
proper nonempty prefixes end in a state belonging to `S`. -/
