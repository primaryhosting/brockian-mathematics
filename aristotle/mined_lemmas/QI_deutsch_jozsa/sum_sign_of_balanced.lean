import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

set_option grind.warning false

namespace QI

variable {n : ℕ}

/-- The sign `(-1)^b` attached to a Boolean value. -/

lemma sum_sign_of_balanced {f : (Fin n → Bool) → Bool} (hf : IsBalanced f) :
    ∑ x : Fin n → Bool, sign (f x) = 0 := by
  classical
  set T : Finset (Fin n → Bool) := Finset.univ.filter (fun x => f x = true) with hTdef
  set F : Finset (Fin n → Bool) := Finset.univ.filter (fun x => f x = false) with hFdef
  have hFeq : F = Finset.univ.filter (fun x : Fin n → Bool => ¬ (f x = true)) := by
    rw [hFdef]; ext x; simp
  have hsplit :
      ∑ x : Fin n → Bool, sign (f x)
        = (∑ x ∈ T, sign (f x)) + ∑ x ∈ F, sign (f x) := by
    rw [hFeq, hTdef]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h1 : (∑ x ∈ T, sign (f x)) = ∑ _x ∈ T, (-1 : ℂ) :=
    Finset.sum_congr rfl (fun x hx => by
      have : f x = true := by rw [hTdef] at hx; simpa using hx
      simp [sign, this])
  have h2 : (∑ x ∈ F, sign (f x)) = ∑ _x ∈ F, (1 : ℂ) :=
    Finset.sum_congr rfl (fun x hx => by
      have : f x = false := by rw [hFdef] at hx; simpa using hx
      simp [sign, this])
  have hcard : (T.card : ℂ) = (F.card : ℂ) := by
    have hT : {x : Fin n → Bool | f x = true}.toFinset = T := by rw [hTdef]; ext x; simp
    have hF : {x : Fin n → Bool | f x = false}.toFinset = F := by rw [hFdef]; ext x; simp
    have hf' : {x : Fin n → Bool | f x = true}.toFinset.card
        = {x : Fin n → Bool | f x = false}.toFinset.card := hf
    rw [hT, hF] at hf'
    exact_mod_cast congrArg (fun m : ℕ => (m : ℂ)) hf'
  rw [hsplit, h1, h2, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hcard]
  ring

/-- **Deutsch–Jozsa.**  Running `H^{⊗n}`, a *single* query to the phase oracle for `f`,
and `H^{⊗n}` again, the all-zeros measurement outcome occurs with probability `1` when
`f` is constant and with probability `0` when `f` is balanced.  Hence one query suffices
to decide constant vs. balanced. -/
