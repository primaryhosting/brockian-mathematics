/-
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Time Hierarchy

A diagonalization proof that more time gives strictly more languages.
-/

open Nat.Partrec Nat.Partrec.Code Denumerable

namespace CS

/-- A *language* is a decision problem on the natural numbers, i.e. a map `ℕ → Bool`.

`TIME t` is the class of languages that some program (a `Nat.Partrec.Code`) decides
within `t x` steps on input `x`, where "steps" are measured by Mathlib's step-indexed
evaluator `Nat.Partrec.Code.evaln`: `evaln k c x` runs the program `c` on input `x`
with fuel `k`, returning `none` if the fuel runs out. -/
def TIME (t : ℕ → ℕ) : Set (ℕ → Bool) :=
  {L | ∃ c : Code, ∀ x, evaln (t x) c x = some (if L x then 1 else 0)}

/-- The diagonal language for the time bound `t`: on input `x`, decode `x` as a program
and accept exactly when that program, run on input `x` with fuel `t x`, fails to output `1`. -/
def diag (t : ℕ → ℕ) : ℕ → Bool :=
  fun x => !(decide (Option.getD (evaln (t x) (ofNat Code x) x) 0 = 1))

/-- Monotonicity of the time classes in the time bound. -/
theorem TIME_mono {t T : ℕ → ℕ} (h : ∀ x, t x ≤ T x) : TIME t ⊆ TIME T := by
  rintro L ⟨c, hc⟩
  exact ⟨c, fun x => evaln_mono (h x) (hc x)⟩

/-- The diagonal language is not decidable in time `t`: this is the diagonalization step. -/
theorem diag_not_mem_TIME (t : ℕ → ℕ) : diag t ∉ TIME t := by
  rintro ⟨c, hc⟩
  set x : ℕ := Encodable.encode c
  have hdec : ofNat Code x = c := Denumerable.ofNat_encode c
  have h := hc x
  have hd : diag t x = !(decide (Option.getD (evaln (t x) c x) 0 = 1)) := by
    rw [diag, hdec]
  rw [h] at hd
  cases hb : diag t x with
  | false => rw [hb] at hd; simp at hd
  | true => rw [hb] at hd; simp at hd

/-- The diagonal language is computable, provided the time bound is. -/
theorem diag_computable {t : ℕ → ℕ} (ht : Computable t) : Computable (diag t) := by
  have h1 : Computable (fun x : ℕ => ((t x, ofNat Code x), x)) :=
    Computable.pair (Computable.pair ht (Computable.ofNat Code)) Computable.id
  have h2 : Computable (fun x : ℕ => evaln (t x) (ofNat Code x) x) :=
    (Nat.Partrec.Code.primrec_evaln.to_comp).comp h1
  have h3 : Computable (fun x : ℕ => Option.getD (evaln (t x) (ofNat Code x) x) 0) :=
    Computable.option_getD h2 (Computable.const 0)
  have h4 : Computable (fun x : ℕ => decide (Option.getD (evaln (t x) (ofNat Code x) x) 0 = 1)) :=
    (Primrec.eq (α := ℕ)).decide.to_comp.comp h3 (Computable.const 1)
  exact Primrec.not.to_comp.comp h4

/-- Non-vacuity check: the empty language is decided in time `x + 1` (by the program `zero`). -/
theorem empty_mem_TIME : (fun _ => false) ∈ TIME (fun x => x + 1) :=
  ⟨Code.zero, fun x => by simp [evaln]⟩

/-- **Time hierarchy theorem.**  For every computable time bound `t` there is a larger time
bound `T` such that strictly more languages are decidable in time `T` than in time `t`.
The witness separating the two classes is the diagonal language `CS.diag t`. -/
theorem time_hierarchy (t : ℕ → ℕ) (ht : Computable t) :
    ∃ T : ℕ → ℕ, (∀ x, t x ≤ T x) ∧ TIME t ⊂ TIME T := by
  -- a code for the diagonal language
  have hg : Computable (fun x : ℕ => if diag t x then 1 else 0) :=
    (Computable.cond (diag_computable ht) (Computable.const 1)
      (Computable.const 0)).of_eq (fun x => by cases diag t x <;> simp)
  have hp : Nat.Partrec (fun x : ℕ => Part.some (if diag t x then 1 else 0)) :=
    Partrec.nat_iff.1 hg.partrec
  obtain ⟨c, hcode⟩ := exists_code.1 hp
  have hex : ∀ x : ℕ, ∃ k, evaln k c x = some (if diag t x then 1 else 0) := by
    intro x
    have : (if diag t x then 1 else 0) ∈ eval c x := by
      rw [hcode]; simp
    exact evaln_complete.1 this
  refine ⟨fun x => max (t x) (Nat.find (hex x)), fun x => le_max_left _ _, ?_⟩
  have hsub : TIME t ⊆ TIME (fun x => max (t x) (Nat.find (hex x))) :=
    TIME_mono (fun x => le_max_left _ _)
  have hmem : diag t ∈ TIME (fun x => max (t x) (Nat.find (hex x))) :=
    ⟨c, fun x => evaln_mono (le_max_right _ _) (Nat.find_spec (hex x))⟩
  refine ⟨hsub, fun hsup => ?_⟩
  exact diag_not_mem_TIME t (hsup hmem)

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

