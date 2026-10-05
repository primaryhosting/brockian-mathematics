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


private theorem pathIn_from_head_aux {l : List σ} {q : σ} :
    ∀ (n : ℕ) (x : List α) (t : σ), x.length ≤ n → PathIn M (q :: l) q t x →
      x ∈ (pathLang M l q q)∗ * pathLang M l q t := by
  intro n
  induction n with
  | zero =>
    intro x t hlen hx
    obtain rfl : x = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    exact Language.mem_mul.mpr ⟨[], Language.nil_mem_kstar _, [], hx, rfl⟩
  | succ n ih =>
    intro x t hlen hx
    rcases pathIn_split M x q t hx with h | ⟨y, z, rfl, hy, hyq, hz⟩
    · exact Language.mem_mul.mpr ⟨[], Language.nil_mem_kstar _, x, h, rfl⟩
    · have hzlen : z.length ≤ n := by
        have hy' : 1 ≤ y.length := by
          cases y with
          | nil => exact absurd rfl hy
          | cons _ _ => simp
        have : y.length + z.length ≤ n + 1 := by simpa using hlen
        omega
      obtain ⟨c, hc, d, hd, rfl⟩ := Language.mem_mul.mp (ih z t hzlen hz)
      refine Language.mem_mul.mpr ⟨y ++ c, cons_mem_kstar hyq hc, d, hd, ?_⟩
      simp

