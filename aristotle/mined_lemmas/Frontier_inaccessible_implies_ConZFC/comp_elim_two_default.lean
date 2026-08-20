import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order Set

/-! ## Cardinal arithmetic of the von Neumann hierarchy below an inaccessible -/

variable {κ : Cardinal.{u}}

/-- Below an inaccessible cardinal `κ`, all the beth-numbers are smaller than `κ`. -/

@[simp] theorem comp_elim_two_default {M : Type*} {k n : ℕ} (v : Fin k → M) (xs : Fin n → M)
    (i j : Fin n) :
    (Sum.elim v xs ∘ Sum.elim (fun a => Sum.inl a)
      (Matrix.vecCons (Sum.inr i) (Matrix.vecCons (Sum.inr j) default) : Fin 2 → _))
      = Sum.elim v ![xs i, xs j] := by
  funext x
  cases x with
  | inl a => simp
  | inr y => fin_cases y <;> simp

