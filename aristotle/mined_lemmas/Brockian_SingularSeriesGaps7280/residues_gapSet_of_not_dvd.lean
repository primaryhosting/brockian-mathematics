import Mathlib

/-!
# Admissible gap ranges and the local factors of the singular series

A finite set `H ⊆ ℤ` (a *tuple*) is **admissible** when, for every prime `p`, the reductions
of the elements of `H` modulo `p` do not cover all of `ℤ/pℤ`.  This is exactly the condition
that every local factor

`localFactor H p = (1 - ν_H(p)/p) * (1 - 1/p)^(-|H|)`

of the Hardy–Littlewood singular series `𝔖(H) = ∏_p localFactor H p` is nonzero (equivalently,
positive), where `ν_H(p)` is the number of residue classes mod `p` occupied by `H`.

A **gap range** is a tuple of the shape `{a, a + d, a + 2d, …, a + (k-1)d}`: `k` points with
constant gap `d`.  The main results characterise which gap ranges are admissible, and in
particular determine all admissible gap ranges of diameter `7280`.
-/

namespace Brockian

/-- The set of residue classes mod `p` occupied by a tuple `H ⊆ ℤ`. -/

lemma residues_gapSet_of_not_dvd {a d : ℤ} {k p : ℕ} (hp : p.Prime) (hpk : p ≤ k)
    (hd : ¬ ((p : ℤ) ∣ d)) : (residues (gapSet a d k) p).card = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdne : ((d : ℤ) : ZMod p) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hd
  have huniv : residues (gapSet a d k) p = Finset.univ := by
    refine Finset.eq_univ_of_forall ?_
    intro x
    set u : ZMod p := (x - (a : ZMod p)) * ((d : ℤ) : ZMod p)⁻¹ with hu
    have hj : u.val < k := lt_of_lt_of_le (ZMod.val_lt u) hpk
    rw [residues, gapSet, Finset.image_image]
    refine Finset.mem_image.2 ⟨u.val, Finset.mem_range.2 hj, ?_⟩
    have hval : ((u.val : ℕ) : ZMod p) = u := ZMod.natCast_rightInverse u
    simp only [Function.comp_apply]
    push_cast
    rw [hval, hu]
    field_simp
    ring
  rw [huniv]
  simp [ZMod.card]

/-- **Characterisation of admissible gap ranges.**  A nonempty gap range with gap `d` and `k`
terms is admissible precisely when every prime `p ≤ k` divides the gap `d`. -/
