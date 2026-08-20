/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset
open scoped BigOperators

namespace CS

/-! ### Basic probabilistic vocabulary

All probabilities are uniform probabilities over finite types, expressed as expectations
of `{0,1}`-valued indicator functions. -/

/-- The `{0,1}`-valued indicator of a boolean. -/

lemma telescope_bound {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool)
    (D : (Fin m → Bool) → Bool) (eps : ℝ) (hm : 0 < m)
    (h : ∀ t < m, |hybProb S f D (t + 1) - hybProb S f D t| < eps / m) :
    |hybProb S f D m - hybProb S f D 0| < eps := by
  set A : ℕ → ℝ := fun t => hybProb S f D t with hA
  have hsum : A m - A 0 = ∑ t ∈ range m, (A (t + 1) - A t) := (Finset.sum_range_sub A m).symm
  have hne : (range m).Nonempty := nonempty_range_iff.mpr hm.ne'
  calc |A m - A 0| = |∑ t ∈ range m, (A (t + 1) - A t)| := by rw [hsum]
    _ ≤ ∑ t ∈ range m, |A (t + 1) - A t| := Finset.abs_sum_le_sum_abs _ _
    _ < ∑ _t ∈ range m, eps / m :=
        Finset.sum_lt_sum_of_nonempty hne fun t htm => h t (mem_range.mp htm)
    _ = eps := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul]
        field_simp

/-! ### Main theorem -/

/-- **The Nisan–Wigderson generator derandomizes from a hard function.**

Let `S` be a combinatorial design: `m` subsets of size `n` of a seed of `ℓ` bits (given as
injections `S i : Fin n → Fin ℓ`) whose pairwise intersections have size at most `d`.
Let `f : (Fin n → Bool) → Bool` and let `D` be any distinguisher on `m` bits.

If `f` cannot be computed with advantage `eps/m` over the trivial guess by *any*
Nisan–Wigderson predictor built out of `D`, `d`-juntas and hard-wired advice bits, then the
Nisan–Wigderson generator `nwGen S f` fools `D` with error `eps`: the acceptance probability
of `D` on a pseudorandom string `nwGen S f x` (uniform seed `x`) differs by less than `eps`
from its acceptance probability on a truly uniform `m`-bit string. -/
