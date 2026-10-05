/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

lemma sum_e5 (m : ZMod 5) : ∑ i : ZMod 5, e5 (i * m) = if m = 0 then 5 else 0 := by
  have huniv : (univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} := by decide
  have expand : ∑ i : ZMod 5, e5 (i * m)
      = 1 + e5 m + e5 m ^ 2 + e5 m ^ 3 + e5 m ^ 4 := by
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    have h0 : e5 ((0 : ZMod 5) * m) = 1 := by simp [e5_zero]
    have h1 : e5 ((1 : ZMod 5) * m) = e5 m := by simp
    have h2 : e5 ((2 : ZMod 5) * m) = e5 m ^ 2 := by
      have := e5_nat_mul 2 m; norm_num at this; exact this
    have h3 : e5 ((3 : ZMod 5) * m) = e5 m ^ 3 := by
      have := e5_nat_mul 3 m; norm_num at this; exact this
    have h4 : e5 ((4 : ZMod 5) * m) = e5 m ^ 4 := by
      have := e5_nat_mul 4 m; norm_num at this; exact this
    rw [h0, h1, h2, h3, h4]
    ring
  rw [expand]
  by_cases hm : m = 0
  · subst hm
    norm_num [e5_zero]
  · simp only [hm, if_false]
    have h5 : e5 m ^ 5 = 1 := e5_pow_five m
    have hne : e5 m - 1 ≠ 0 := sub_ne_zero.mpr (e5_ne_one hm)
    have key : (e5 m - 1) * (1 + e5 m + e5 m ^ 2 + e5 m ^ 3 + e5 m ^ 4) = 0 := by
      have : (e5 m - 1) * (1 + e5 m + e5 m ^ 2 + e5 m ^ 3 + e5 m ^ 4) = e5 m ^ 5 - 1 := by
        ring
      rw [this, h5, sub_self]
    exact (mul_eq_zero.mp key).resolve_left hne

/-! ### Diagonalization by the discrete Fourier matrix -/

/-- The discrete Fourier matrix. -/
