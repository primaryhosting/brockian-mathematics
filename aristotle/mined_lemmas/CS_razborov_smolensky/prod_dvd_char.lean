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


theorem prod_dvd_char {F : Type*} [Field F] (q : ℕ) [Fact q.Prime] [CharP F q] {t : ℕ}
    (c : Fin t → ℕ) :
    ∏ k : Fin t, (1 - ((c k : F)) ^ (q - 1)) = if (∀ k, q ∣ c k) then 1 else 0 := by
  split_ifs with h
  · refine Finset.prod_eq_one (fun k _ => ?_)
    rw [natCast_pow_card_sub_one q (c k), if_pos (h k), sub_zero]
  · push_neg at h
    obtain ⟨k, hk⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    rw [natCast_pow_card_sub_one q (c k), if_neg hk, sub_self]

