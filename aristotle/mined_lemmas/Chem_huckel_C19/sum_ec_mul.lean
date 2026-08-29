import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex Finset

namespace Chem

/-- `Fin 19` carries the commutative ring structure of `ZMod 19`
(the two types, and their additive group structures, are definitionally equal). -/
noncomputable local instance : CommRing (Fin 19) := (inferInstance : CommRing (ZMod 19))

/-- A primitive 19-th root of unity. -/

lemma sum_ec_mul (d : Fin 19) :
    (∑ k : Fin 19, ec (k * d)) = if d = 0 then (19 : ℂ) else 0 := by
  have hstep : ∀ k : Fin 19, ec (k * d) = ec d ^ (k : ℕ) := by
    intro k
    conv_lhs => rw [← Fin.cast_val_eq_self k]
    exact ec_natCast_mul k.val d
  rw [Finset.sum_congr rfl (fun k _ => hstep k)]
  rw [Fin.sum_univ_eq_sum_range (fun j => ec d ^ j) 19]
  by_cases hd : d = 0
  · subst hd
    simp [ec_zero]
  · have hne : ec d ≠ 1 := by
      have hv : d.val ≠ 0 := by
        intro h
        exact hd (Fin.ext (by simpa using h))
      exact zeta19_primitive.pow_ne_one_of_pos_of_lt hv d.isLt
    have hpow : ec d ^ 19 = 1 := by
      rw [ec, ← pow_mul, mul_comm, pow_mul, zeta19_pow19, one_pow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div, if_neg hd]

