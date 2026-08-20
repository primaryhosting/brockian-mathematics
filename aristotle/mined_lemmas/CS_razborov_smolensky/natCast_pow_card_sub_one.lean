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


theorem natCast_pow_card_sub_one {F : Type*} [Field F] (q : ℕ) [Fact q.Prime] [CharP F q]
    (k : ℕ) : ((k : F)) ^ (q - 1) = if q ∣ k then 0 else 1 := by
  have hp := Fact.out (p := q.Prime)
  have h : ((k : F)) = (ZMod.castHom (dvd_refl q) F) (k : ZMod q) := by simp
  split_ifs with hd
  · have h0 : (k : F) = 0 := by
      rw [h, (ZMod.natCast_eq_zero_iff k q).2 hd, map_zero]
    rw [h0]
    exact zero_pow (by have := hp.two_le; omega)
  · have hk : ((k : ZMod q)) ≠ 0 := fun hc => hd ((ZMod.natCast_eq_zero_iff k q).1 hc)
    rw [h, ← map_pow, ZMod.pow_card_sub_one_eq_one hk, map_one]

/-- Summing indicators over a selected set counts the selected witnesses. -/
