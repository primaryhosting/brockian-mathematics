/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- The Hückel (adjacency) matrix of the cycle graph `C n`, with vertices indexed by `ZMod n`:
vertex `i` is joined to `i + 1` and to `i - 1`.  For `n ≥ 3` this is exactly the adjacency matrix
of the simple cycle graph `C n`; for `n = 1, 2` it is the circulant matrix `S + S⁻¹` (`S` the
cyclic shift), which is the convention under which the Hückel spectrum formula holds. -/

lemma chi_orthogonality (n : ℕ) [NeZero n] (s : ZMod n) :
    ∑ t : ZMod n, chi n (t * s) = if s = 0 then (n : ℂ) else 0 := by
  have hcomm : ∀ t : ZMod n, chi n (t * s) = (chi n s) ^ t.val := by
    intro t; rw [mul_comm, chi_mul]
  simp only [hcomm]
  rw [sum_zmod_eq_sum_range]
  have hval : ∀ m ∈ Finset.range n, ((m : ZMod n)).val = m := by
    intro m hm; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hm)
  rw [Finset.sum_congr rfl (fun m hm => by rw [hval m hm])]
  by_cases hs : s = 0
  · subst hs; simp [chi_zero]
  · rw [if_neg hs]
    have hne : chi n s ≠ 1 := fun h => hs ((chi_eq_one_iff n s).1 h)
    have hpow : (chi n s) ^ n = 1 := by
      rw [chi, ← pow_mul, mul_comm, pow_mul, zeta_pow_card, one_pow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

