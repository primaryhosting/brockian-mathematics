import Mathlib

/-!
# Kleene Regex Dfa
Category: Computer Science
Target: CS.kleene_regex_dfa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Computability

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

universe u v

/-! ## Part 1: the language of a regular expression is accepted by a finite DFA

We use the Myhill–Nerode theorem: it suffices to show that a regular expression has only
finitely many left quotients (Brzozowski derivatives, viewed as languages). -/

section RegexToDFA

variable {α : Type u}


theorem pathLang_insert_le (S : Finset σ) (r q : σ) : ∀ (x : List α) (p : σ),
    x ∈ pathLang M (insert r S) p q →
    x ∈ pathLang M S p q + pathLang M S p r * (pathLang M S r r)∗ * pathLang M S r q := by
  intro x
  induction x with
  | nil =>
    intro p h
    obtain ⟨h1, -⟩ := h
    rw [DFA.evalFrom_nil] at h1
    subst h1
    exact Or.inl (nil_mem_pathLang M S p)
  | cons a x' ih =>
    intro p h
    obtain ⟨h1, h2⟩ := h
    rcases eq_or_ne x' [] with rfl | hx'
    · refine Or.inl ⟨h1, fun u v huv hu hv => ?_⟩
      rcases u with _ | ⟨b, u⟩
      · exact absurd rfl hu
      · rcases u with _ | ⟨c, u⟩
        · simp only [List.cons_append, List.nil_append, List.cons.injEq] at huv
          exact absurd huv.2 hv
        · simp at huv
    · set p' := M.step p a with hp'def
      have hstep : ∀ w : List α, M.evalFrom p (a :: w) = M.evalFrom p' w := by
        intro w; rw [DFA.evalFrom_cons]
      have hx'mem : x' ∈ pathLang M (insert r S) p' q := by
        refine ⟨by rw [← hstep]; exact h1, fun u v huv hu hv => ?_⟩
        have h3 := h2 (a :: u) v (by rw [List.cons_append, huv]) (by simp) hv
        rwa [hstep] at h3
      have hp'S : p' ∈ insert r S := by
        have h3 := h2 [a] x' rfl (by simp) hx'
        rwa [DFA.evalFrom_singleton] at h3
      have ha : [a] ∈ pathLang M S p p' := singleton_mem_pathLang M S p a
      rcases ih p' hx'mem with h3 | h3
      · rcases eq_or_ne p' r with hpr | hpr
        · subst hpr
          refine Or.inr ⟨[a] ++ [], ⟨[a], ha, [], Language.nil_mem_kstar _, rfl⟩, x', h3, ?_⟩
          simp
        · exact Or.inl (pathLang_mul_le M (Finset.mem_of_mem_insert_of_ne hp'S hpr)
            ⟨[a], ha, x', h3, rfl⟩)
      · obtain ⟨w, ⟨c, hc, d, hd, rfl⟩, e, he, rfl⟩ := h3
        rcases eq_or_ne p' r with hpr | hpr
        · subst hpr
          refine Or.inr ⟨[a] ++ (c ++ d), ⟨[a], ha, c ++ d, ?_, rfl⟩, e, he, by simp⟩
          exact mul_kstar_le_kstar (a := pathLang M S p' p') ⟨c, hc, d, hd, rfl⟩
        · refine Or.inr ⟨([a] ++ c) ++ d, ⟨[a] ++ c,
            pathLang_mul_le M (Finset.mem_of_mem_insert_of_ne hp'S hpr) ⟨[a], ha, c, hc, rfl⟩,
            d, hd, rfl⟩, e, he, by simp⟩

/-- The Kleene recursion: adding one allowed intermediate state `r`. -/
