import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# MOD_p is not approximable by low degree functions over a field of characteristic q

This is the second half of Smolensky's argument: if the function `x ↦ ζ^{|x|}`
(`ζ` a primitive `p`-th root of unity in a field `F` of characteristic `q`) agrees
with a function of degree `D` on a set `G` of inputs, then `G` is small.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- The monomial `∏_{i ∈ S} ζ^{x_i}` in the transformed variables. -/

lemma natCast_pow_char {q : ℕ} (hq : q.Prime) [CharP F q] (m : ℕ) :
    ((m : F)) ^ (q - 1) = if q ∣ m then 0 else 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hcast : (m : F) = (ZMod.castHom (dvd_refl q) F) (m : ZMod q) := by simp
  rw [hcast, ← map_pow]
  by_cases h : q ∣ m
  · rw [if_pos h, (ZMod.natCast_eq_zero_iff m q).2 h,
      zero_pow (by have := hq.two_le; omega), map_zero]
  · rw [if_neg h, ZMod.pow_card_sub_one_eq_one
      (fun hc => h ((ZMod.natCast_eq_zero_iff m q).1 hc)), map_one]

/-- At most half of the subsets `S` of a set of indices satisfy `q ∣ #(S ∩ ones)`,
provided there is at least one index with `bl i = true`. -/
