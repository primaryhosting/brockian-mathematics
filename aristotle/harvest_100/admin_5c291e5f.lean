import Mathlib
/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The time hierarchy theorem, by diagonalization, in the step-indexed model of
computation provided by Mathlib's Gödel-numbered partial recursive functions
(`Nat.Partrec.Code`) together with its step-indexed evaluator
`Nat.Partrec.Code.evaln : ℕ → Code → ℕ → Option ℕ`.

For a time bound `t : ℕ → ℕ`, `CS.TIME t` is the set of languages `L : ℕ → Bool`
for which some code `c` outputs `L x` on input `x` within `t x` steps.

The main theorem `CS.time_hierarchy` states: for every computable time bound `f`
there is a larger time bound `g` with `TIME f ⊊ TIME g`; i.e. more time gives
strictly more languages.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code Denumerable

/-- A language: a decision problem on the natural numbers. -/
abbrev Language := ℕ → Bool

/-- `TIME t` is the class of languages decided within `t x` steps on input `x`,
where a step budget is measured by Mathlib's step-indexed evaluator `evaln`. -/
def TIME (t : ℕ → ℕ) : Set Language :=
  {L | ∃ c : Code, ∀ x, evaln (t x) c x = some (if L x then 1 else 0)}

/-- More time can only decide more languages. -/
theorem TIME_mono {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) : TIME t₁ ⊆ TIME t₂ := by
  rintro L ⟨c, hc⟩
  exact ⟨c, fun x => evaln_mono (h x) (hc x)⟩

/-- The diagonal language for a time bound `f`: on input `x`, run the `x`-th code on
input `x` for `f x` steps, and output the opposite answer. -/
def diag (f : ℕ → ℕ) : Language :=
  fun x => decide (evaln (f x) (ofNat Code x) x ≠ some 1)

/-- Diagonalization: the diagonal language is not decidable in time `f`. -/
theorem diag_not_mem_TIME (f : ℕ → ℕ) : diag f ∉ TIME f := by
  rintro ⟨c, hc⟩
  set e := Encodable.encode c
  have he : (ofNat Code e) = c := Denumerable.ofNat_encode c
  have hx := hc e
  have hd : diag f e = decide (evaln (f e) c e ≠ some 1) := by
    simp [diag, he]
  by_cases h : evaln (f e) c e = some 1
  · rw [h] at hd
    simp at hd
    rw [hd] at hx
    simp [h] at hx
  · rw [hd] at hx
    simp [h] at hx

/-- The diagonal language is computable when the time bound is. -/
theorem diag_computable {f : ℕ → ℕ} (hf : Computable f) : Computable (diag f) := by
  have h1 : Computable fun x : ℕ => evaln (f x) (ofNat Code x) x :=
    (Nat.Partrec.Code.primrec_evaln.to_comp).comp
      (((hf.pair (Primrec.ofNat Code).to_comp)).pair Computable.id)
  have hb : Computable fun x : ℕ =>
      @BEq.beq (Option ℕ) instBEqOfDecidableEq (evaln (f x) (ofNat Code x) x) (some 1) :=
    Primrec.beq.to_comp.comp h1 (Computable.const (some 1))
  exact (Primrec.not.to_comp.comp hb).of_eq (fun x => by simp [diag, instBEqOfDecidableEq])

/-- Any computable language is decidable within some time bound. -/
theorem exists_TIME_of_computable {L : Language} (hL : Computable L) :
    ∃ t : ℕ → ℕ, L ∈ TIME t := by
  have hn : Computable fun x : ℕ => (if L x then 1 else 0 : ℕ) :=
    (Computable.cond hL (Computable.const 1) (Computable.const 0)).of_eq
      (fun n => by cases L n <;> simp)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (Nat.Partrec.of_eq
    (Partrec.nat_iff.1 hn.partrec) (fun n => rfl))
  have hmem : ∀ x : ℕ, ∃ k, evaln k c x = some (if L x then 1 else 0) := by
    intro x
    have : (if L x then 1 else 0 : ℕ) ∈ eval c x := by
      rw [hc]; simp
    exact evaln_complete.1 this
  choose t ht using hmem
  exact ⟨t, c, ht⟩

/-- **Time hierarchy theorem.** For every computable time bound `f` there is a larger
time bound `g` such that the languages decidable in time `g` strictly contain those
decidable in time `f`: more time gives strictly more languages.

The witness separating the two classes is the diagonal language `CS.diag f`. -/
theorem time_hierarchy {f : ℕ → ℕ} (hf : Computable f) :
    ∃ g : ℕ → ℕ, (∀ n, f n ≤ g n) ∧ TIME f ⊂ TIME g := by
  obtain ⟨t, ht⟩ := exists_TIME_of_computable (diag_computable hf)
  refine ⟨fun n => max (f n) (t n), fun n => le_max_left _ _, ?_⟩
  refine ⟨TIME_mono fun n => le_max_left _ _, ?_⟩
  intro hsub
  exact diag_not_mem_TIME f (hsub (TIME_mono (fun n => le_max_right _ _) ht))

-- The proof uses only the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
#print axioms CS.time_hierarchy

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

