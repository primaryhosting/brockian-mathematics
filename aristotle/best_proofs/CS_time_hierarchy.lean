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
def DTIME (f : ℕ → ℕ) : Set Lang :=
  {L | ∃ c : Code, ∀ n, evaln (f n) c n = some (if L n then 1 else 0)}

/-- More time can only help: time bounds that dominate decide at least as much. -/
theorem DTIME_mono {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) : DTIME f ⊆ DTIME g := by
  rintro L ⟨c, hc⟩
  exact ⟨c, fun n => evaln_mono (h n) (hc n)⟩

section

variable (f : ℕ → ℕ)

/-- The diagonal language for the time bound `f`: input `n` is accepted iff the `n`-th
program, run on input `n` with budget `f n`, fails to output `1`. -/
def diagLang : Lang := fun n =>
  decide (evaln (f n) (Denumerable.ofNat Code n) n ≠ some 1)

/-- Diagonalization: the diagonal language is not decidable within time `f`. -/
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
theorem computable_diagLang (hf : Computable f) : Computable (diagLang f) := by
  have h1 : Computable fun n : ℕ => evaln (f n) (Denumerable.ofNat Code n) n :=
    (Nat.Partrec.Code.primrec_evaln.to_comp).comp
      (((hf.pair (Computable.ofNat Code)).pair Computable.id))
  have h2 : Computable fun n : ℕ =>
      decide (evaln (f n) (Denumerable.ofNat Code n) n = some 1) :=
    (Primrec₂.to_comp Primrec.eq.decide).comp h1 (Computable.const (some 1))
  have h3 := (Primrec.not.to_comp).comp h2
  exact h3.of_eq fun n => by simp [diagLang, decide_not]

end

/-- Completeness of the model: every computable language is decided within *some*
time bound, so the classes `DTIME f` are not vacuous. -/
theorem mem_DTIME_of_computable (L : Lang) (hL : Computable L) : ∃ g : ℕ → ℕ, L ∈ DTIME g := by
  classical
  have hF : Computable fun n : ℕ => (if L n then 1 else 0 : ℕ) :=
    (Computable.cond hL (Computable.const 1) (Computable.const 0)).of_eq
      (fun n => by cases L n <;> simp)
  obtain ⟨c, hcode⟩ :=
    Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hF.partrec)
  have hex : ∀ n, ∃ k, (if L n then 1 else 0 : ℕ) ∈ evaln k c n := by
    intro n
    refine evaln_complete.1 ?_
    rw [hcode]
    simp
  choose k hk using hex
  exact ⟨k, c, hk⟩

/-- **Time hierarchy theorem.**  For every computable time bound `f` there is a larger
time bound `g` such that strictly more languages can be decided in time `g` than in
time `f`: `DTIME f ⊊ DTIME g`.  The separating witness is the diagonal language
`diagLang f`, which by construction differs from the language of every program that
runs within time `f`. -/
theorem time_hierarchy (f : ℕ → ℕ) (hf : Computable f) :
    ∃ g : ℕ → ℕ, (∀ n, f n ≤ g n) ∧ DTIME f ⊂ DTIME g := by
  obtain ⟨g₀, hg₀⟩ := mem_DTIME_of_computable (diagLang f) (computable_diagLang f hf)
  refine ⟨fun n => max (f n) (g₀ n), fun n => le_max_left _ _,
    DTIME_mono (fun n => le_max_left _ _), fun hsub => ?_⟩
  exact diagLang_not_mem f (hsub (DTIME_mono (fun n => le_max_right _ _) hg₀))

end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

