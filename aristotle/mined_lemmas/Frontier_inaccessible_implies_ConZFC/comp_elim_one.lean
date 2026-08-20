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

@[simp] theorem comp_elim_one {M : Type*} {k n : ℕ} (v : Fin k → M) (xs : Fin n → M) (j : Fin n) :
    (Sum.elim v xs ∘ Sum.elim (fun a => Sum.inl a) (fun _ : Fin 1 => Sum.inr j))
      = Sum.elim v (fun _ => xs j) := by
  funext x; cases x <;> simp

