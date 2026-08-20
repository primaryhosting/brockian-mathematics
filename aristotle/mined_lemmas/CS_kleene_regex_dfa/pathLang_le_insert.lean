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
open scoped Pointwise
open scoped Computability
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

universe u v

/-- A language is *regex-expressible* if some regular expression matches exactly it. -/

lemma pathLang_le_insert [DecidableEq σ] (k : σ) (S : Finset σ) :
    ∀ (N : ℕ) (i j : σ) (w : List α), w.length ≤ N → w ∈ pathLang M (insert k S) i j →
      w ∈ pathLang M S i j + pathLang M S i k * (pathLang M S k k)∗ * pathLang M S k j := by
  intro N
  induction N with
  | zero =>
      intro i j w hlen hw
      obtain ⟨hw1, -⟩ := hw
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
      subst hw0
      exact Or.inl ⟨hw1, fun n _ hn => by simp at hn⟩
  | succ N ih =>
      intro i j w hlen hw
      obtain ⟨hw1, hw2⟩ := hw
      by_cases hex : ∃ n, 0 < n ∧ n < w.length ∧ M.evalFrom i (w.take n) = k
      · obtain ⟨hm0, hmlt, hmk⟩ := Nat.find_spec hex
        set m := Nat.find hex
        have hmin : ∀ n, n < m → ¬ (0 < n ∧ n < w.length ∧ M.evalFrom i (w.take n) = k) :=
          fun n hn => Nat.find_min hex hn
        have hu : w.take m ∈ pathLang M S i k := by
          refine ⟨hmk, ?_⟩
          intro n hn hlt
          rw [List.length_take, min_eq_left hmlt.le] at hlt
          rw [List.take_take, min_eq_left hlt.le]
          have h1 : M.evalFrom i (w.take n) ∈ insert k S := hw2 n hn (by omega)
          have h2 : M.evalFrom i (w.take n) ≠ k := fun hc => hmin n hlt ⟨hn, by omega, hc⟩
          exact Finset.mem_of_mem_insert_of_ne h1 h2
        have hv : w.drop m ∈ pathLang M (insert k S) k j := by
          refine ⟨?_, ?_⟩
          · have h := M.evalFrom_of_append i (w.take m) (w.drop m)
            rw [List.take_append_drop, hw1, hmk] at h
            exact h.symm
          · intro n hn hlt
            rw [List.length_drop] at hlt
            have key : w.take (m + n) = w.take m ++ (w.drop m).take n := List.take_add
            have h3 : M.evalFrom i (w.take (m + n)) ∈ insert k S :=
              hw2 (m + n) (by omega) (by omega)
            rw [key, M.evalFrom_of_append, hmk] at h3
            exact h3
        have hvlen : (w.drop m).length ≤ N := by
          rw [List.length_drop]; omega
        have hrec := ih k j (w.drop m) hvlen hv
        have hvstar : w.drop m ∈ (pathLang M S k k)∗ * pathLang M S k j := by
          rcases hrec with h | h
          · exact Language.mem_mul.mpr ⟨[], Language.nil_mem_kstar _, _, h, by simp⟩
          · obtain ⟨p, hp, t, ht, hpt⟩ := Language.mem_mul.mp h
            obtain ⟨a, ha, b, hb, hab⟩ := Language.mem_mul.mp hp
            exact Language.mem_mul.mpr ⟨p, hab ▸ cons_mem_kstar ha hb, t, ht, hpt⟩
        obtain ⟨z, hz, t, ht, hzt⟩ := Language.mem_mul.mp hvstar
        refine Or.inr (Language.mem_mul.mpr
          ⟨w.take m ++ z, Language.mem_mul.mpr ⟨w.take m, hu, z, hz, rfl⟩, t, ht, ?_⟩)
        rw [List.append_assoc, hzt, List.take_append_drop]
      · refine Or.inl ⟨hw1, ?_⟩
        intro n hn hlt
        have h1 := hw2 n hn hlt
        have h2 : M.evalFrom i (w.take n) ≠ k := fun hc => hex ⟨n, hn, hlt, hc⟩
        exact Finset.mem_of_mem_insert_of_ne h1 h2

/-- Kleene's recursion: adding one more allowed intermediate state `k`. -/
