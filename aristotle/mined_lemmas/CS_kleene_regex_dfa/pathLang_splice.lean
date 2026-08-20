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

theorem pathLang_splice {T : Finset σ} {i j k : σ} (hk : k ∈ T) :
    pathLang M T i k * pathLang M T k j ≤ pathLang M T i j := by
  rintro w hw
  rw [Language.mem_mul] at hw
  obtain ⟨u, ⟨hu, hui⟩, v, ⟨hv, hvi⟩, rfl⟩ := hw
  refine ⟨by rw [M.evalFrom_of_append, hu, hv], ?_⟩
  intro p q hpq hp hq
  rcases List.append_eq_append_iff.1 hpq with ⟨t, hut, hqt⟩ | ⟨t, hpt, hvt⟩
  · rcases eq_or_ne t [] with rfl | ht
    · rw [List.append_nil] at hut
      subst hut
      rw [hu]
      exact hk
    · exact hui p t hut.symm hp ht
  · subst hpt
    rw [M.evalFrom_of_append, hu]
    rcases eq_or_ne t [] with rfl | ht
    · simpa using hk
    · exact hvi t q hvt.symm ht hq

