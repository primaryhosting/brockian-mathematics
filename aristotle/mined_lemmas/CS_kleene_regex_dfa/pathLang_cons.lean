import Mathlib

/-!
# Kleene Regex Dfa
Category: Computer Science
Target: CS.kleene_regex_dfa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Kleene's theorem: over a finite alphabet, a language is denoted by a regular expression
if and only if it is accepted by a deterministic finite automaton with finitely many states.
-/

open Language Computability

namespace CS

variable {α : Type*}


theorem pathLang_cons (l : List σ) (q s t : σ) :
    pathLang M (q :: l) s t =
      pathLang M l s t + pathLang M l s q * (pathLang M l q q)∗ * pathLang M l q t := by
  have hq : q ∈ q :: l := List.mem_cons_self
  have hsub : ∀ p ∈ l, p ∈ q :: l := fun p hp => List.mem_cons_of_mem _ hp
  ext x
  rw [Language.mem_add]
  simp only [mem_pathLang]
  constructor
  · intro h
    rcases pathIn_split M x s t h with h | ⟨y, z, rfl, -, hyq, hz⟩
    · exact Or.inl h
    · right
      obtain ⟨c, hc, d, hd, rfl⟩ := Language.mem_mul.mp (pathIn_from_head M hz)
      exact Language.mem_mul.mpr ⟨y ++ c, Language.mem_mul.mpr ⟨y, hyq, c, hc, rfl⟩, d, hd, by simp⟩
  · rintro (h | h)
    · exact pathIn_mono M hsub x s t h
    · obtain ⟨e, he, d, hd, rfl⟩ := Language.mem_mul.mp h
      obtain ⟨y, hy, c, hc, rfl⟩ := Language.mem_mul.mp he
      have h1 : PathIn M (q :: l) s q y := pathIn_mono M hsub y s q hy
      have h2 : PathIn M (q :: l) q q c := by
        obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hc
        refine pathIn_of_kstar M hq (Language.join_mem_kstar fun z hz => ?_)
        exact pathIn_mono M hsub z q q (hL z hz)
      have h3 : PathIn M (q :: l) q t d := pathIn_mono M hsub d q t hd
      exact pathIn_append M hq (y ++ c) s d t (pathIn_append M hq y s c q h1 h2) h3

/-! ### Building the regular expression -/

/-- A regular expression matching exactly the one-letter words `[a]` for `a ∈ l`. -/
