import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem prod_dvd_eval {F : Type*} [Field F] (q : ℕ) [Fact q.Prime] [CharP F q] {t k : ℕ}
    (S : Finset (Fin k)) (sel : Fin t → Fin k → Bool) (g : Fin k → F) (w : Fin k → Bool)
    (hg : ∀ j ∈ S, g j = ind F (w j)) :
    ∏ κ : Fin t, (1 - (∑ j ∈ S.filter (fun j => sel κ j = true), g j) ^ (q - 1))
      = if (∀ κ : Fin t, q ∣ (S.filter (fun j => sel κ j = true ∧ w j = true)).card)
        then 1 else 0 := by
  have hstep : ∀ κ : Fin t, (∑ j ∈ S.filter (fun j => sel κ j = true), g j)
      = ((S.filter (fun j => sel κ j = true ∧ w j = true)).card : F) := by
    intro κ
    rw [← sum_ind_eq S (sel κ) w]
    exact Finset.sum_congr rfl (fun j hj => hg j (Finset.mem_filter.1 hj).1)
  simp only [hstep]
  exact prod_dvd_char q (fun κ => (S.filter (fun j => sel κ j = true ∧ w j = true)).card)

namespace Circuit

variable {n : ℕ}

/-- The randomness used by the approximating polynomial: for each gate and each of the `t`
rounds, a random subset of the gate indices. -/
abbrev Rand (C : Circuit n) (t : ℕ) := Fin C.size → Fin t → Fin C.size → Bool

/-- The random low degree approximation of the value at gate `i`. -/
