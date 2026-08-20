import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem natCast_pow_q (F : Type*) [Field F] (q : ℕ) [hq : Fact q.Prime] [CharP F q] (k : ℕ) :
    ((k : F)) ^ (q - 1) = if q ∣ k then 0 else 1 := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  have hmap : ((k : F)) = (ZMod.castHom (dvd_refl q) F) (k : ZMod q) := by simp
  split
  · rename_i h
    have h0 : (k : F) = 0 := by
      rw [hmap, (ZMod.natCast_eq_zero_iff k q).2 h, map_zero]
    rw [h0]
    exact zero_pow (by have := hq.out.two_le; omega)
  · rename_i h
    have hne : ((k : ZMod q)) ≠ 0 := fun hc => h ((ZMod.natCast_eq_zero_iff k q).1 hc)
    rw [hmap, ← map_pow, ZMod.pow_card_sub_one_eq_one hne, map_one]

/-! ### At most half of all subsets have weight divisible by `q` -/

/-- If some coordinate `i₀` carries weight, then at most half of all subsets of `Fin m` have
a weight divisible by `q`. -/
