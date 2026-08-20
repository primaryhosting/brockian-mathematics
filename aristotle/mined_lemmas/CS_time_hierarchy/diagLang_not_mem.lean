import Mathlib

/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Statement: The time hierarchy theorem: more time gives strictly more languages (diagonalization).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- A language: a decision problem on natural-number-encoded inputs. -/
abbrev Lang := ℕ → Bool

/-- `DTIME f` is the class of languages `L` decided by some program (a code for a
partial recursive function) which, when run on input `n` with a budget of `f n`
computation steps (Kleene-style step-bounded evaluation `evaln`), halts and outputs
`1` if `n ∈ L` and `0` otherwise. -/

theorem diagLang_not_mem : diagLang f ∉ DTIME f := by
  rintro ⟨c, hc⟩
  set n := Encodable.encode c with hn
  have hcn : Denumerable.ofNat Code n = c := by
    simp [hn]
  have h := hc n
  by_cases hL : diagLang f n
  · rw [if_pos hL] at h
    have : evaln (f n) (Denumerable.ofNat Code n) n ≠ some 1 := by
      simpa [diagLang] using hL
    exact this (by rw [hcn]; exact h)
  · rw [if_neg hL] at h
    have : ¬ (evaln (f n) (Denumerable.ofNat Code n) n ≠ some 1) := by
      simpa [diagLang] using hL
    rw [hcn] at this
    rw [not_not] at this
    rw [h] at this
    exact absurd this (by decide)

/-- The diagonal language is computable when the time bound is. -/
