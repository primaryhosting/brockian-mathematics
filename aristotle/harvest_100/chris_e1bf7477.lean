import Mathlib

/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

open Nat.Partrec Nat.Partrec.Code Denumerable Encodable

/-- A language: a decision problem whose instances are encoded as natural numbers. -/
abbrev Language : Type := ℕ → Bool

/-- `DTIME t` is the class of languages decided by some partial recursive program
(a `Nat.Partrec.Code`) within `t n` steps on input `n`, where "steps" is measured by the
step-indexed evaluator `Nat.Partrec.Code.evaln`: the machine must output `1` on inputs in the
language and `0` on inputs outside it, using at most `t n` fuel. -/
def DTIME (t : ℕ → ℕ) : Set Language :=
  {L | ∃ c : Code, ∀ n : ℕ, evaln (t n) c n = some (if L n then 1 else 0)}

/-- Time classes are monotone in the time bound. -/
theorem DTIME_mono {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) : DTIME t₁ ⊆ DTIME t₂ := by
  rintro L ⟨c, hc⟩
  exact ⟨c, fun n => evaln_mono (h n) (hc n)⟩

/-- The diagonal language for the time bound `t`: the input `n` is in the language exactly when
the `n`-th program, run on the input `n`, fails to output `1` within `t n` steps. -/
def diag (t : ℕ → ℕ) : Language :=
  fun n => decide (evaln (t n) (ofNat Code n) n ≠ some 1)

/-- Diagonalization: the diagonal language is not decidable within the time bound `t`. -/
theorem diag_not_mem_DTIME (t : ℕ → ℕ) : diag t ∉ DTIME t := by
  rintro ⟨c, hc⟩
  set n : ℕ := encode c with hn
  have hcode : ofNat Code n = c := by rw [hn, ofNat_encode]
  have hval : evaln (t n) c n = some (if diag t n then 1 else 0) := hc n
  have hd : diag t n = decide (evaln (t n) c n ≠ some 1) := by
    rw [diag, hcode]
  by_cases hb : diag t n
  · -- the language says "does not output 1", yet the program outputs 1
    have h1 : evaln (t n) c n = some 1 := by rw [hval, if_pos hb]
    rw [hd, h1] at hb
    simp at hb
  · -- the language says "outputs 1", yet the program outputs 0
    have h0 : evaln (t n) c n = some 0 := by
      rw [hval, if_neg hb]
    rw [hd, h0] at hb
    simp at hb

/-- The characteristic function of the diagonal language is computable, provided the time bound
is computable. -/
theorem computable_diag_char {t : ℕ → ℕ} (ht : Computable t) :
    Computable (fun n : ℕ => if diag t n then 1 else 0) := by
  have heqp : Primrec fun p : Option ℕ × Option ℕ => decide (p.1 = p.2) := by
    obtain ⟨_, h⟩ := (Primrec.eq (α := Option ℕ))
    exact h.of_eq fun p => by simp
  have hev : Computable fun n : ℕ => evaln (t n) (ofNat Code n) n :=
    primrec_evaln.to_comp.comp
      ((ht.pair (Primrec.ofNat Code).to_comp).pair Computable.id)
  have hd : Computable fun n : ℕ => decide (evaln (t n) (ofNat Code n) n = some 1) :=
    heqp.to_comp.comp (hev.pair (Computable.const (some 1)))
  have hcond := Computable.cond hd (Computable.const (0 : ℕ)) (Computable.const 1)
  exact hcond.of_eq fun n => by
    by_cases h : evaln (t n) (ofNat Code n) n = some 1 <;> simp [diag, h]

/-- A computable language lies in `DTIME t'` for some time bound `t'`. -/
theorem exists_time_bound {L : Language} (h : Computable fun n : ℕ => if L n then 1 else 0) :
    ∃ t' : ℕ → ℕ, L ∈ DTIME t' := by
  obtain ⟨c, hc⟩ := exists_code.1 (Partrec.nat_iff.1 h.partrec)
  have hex : ∀ n : ℕ, ∃ k : ℕ, evaln k c n = some (if L n then 1 else 0) := by
    intro n
    have hmem : (if L n then 1 else 0) ∈ c.eval n := by
      rw [hc]; simp
    obtain ⟨k, hk⟩ := evaln_complete.1 hmem
    exact ⟨k, hk⟩
  refine ⟨fun n => Nat.find (hex n), c, fun n => Nat.find_spec (hex n)⟩

/-- **Time hierarchy theorem** (diagonalization form).

For every computable time bound `t` there is a strictly larger time bound `t'` such that the
class of languages decidable in time `t` is a *strict* subclass of those decidable in time `t'`:
more time gives strictly more languages. The witness separating the two classes is the diagonal
language `CS.diag t`. -/
theorem time_hierarchy (t : ℕ → ℕ) (ht : Computable t) :
    ∃ t' : ℕ → ℕ, (∀ n, t n ≤ t' n) ∧ DTIME t ⊂ DTIME t' := by
  obtain ⟨s, hs⟩ := exists_time_bound (computable_diag_char ht)
  refine ⟨fun n => max (t n) (s n), fun n => le_max_left _ _, ?_⟩
  constructor
  · exact DTIME_mono fun n => le_max_left _ _
  · intro hsub
    exact diag_not_mem_DTIME t (hsub (DTIME_mono (fun n => le_max_right _ _) hs))

end CS

