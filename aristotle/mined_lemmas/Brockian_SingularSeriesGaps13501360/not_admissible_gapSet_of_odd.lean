import Mathlib

/-!
# Admissible gaps and the Hardy–Littlewood singular series, gaps 1350–1360

For a prime gap `g` one considers the two–element pattern `{0, g}`: a pair of primes
`(n, n + g)`.  The pattern is *admissible* when, for every prime `p`, the residues of the
pattern modulo `p` do not cover all of `ZMod p` (otherwise one of `n`, `n + g` is divisible
by `p` for every `n`, and the pair can occur only finitely often).

The Hardy–Littlewood singular series for this pattern is
`𝔖(g) = 2 C₂ ∏_{p ∣ g, p odd} (p-1)/(p-2)` for even `g`, and `𝔖(g) = 0` for odd `g`,
where `C₂` is the twin prime constant.  We work with the normalised quantity
`𝔖(g) / (2 C₂)`, which avoids having to introduce the (convergent, but analytically
delicate) Euler product defining `C₂`.

The main results are:
* `Brockian.admissible_gapSet_iff` — `{0, g}` is admissible iff `g` is even (`g > 0`);
* `Brockian.normalizedSingularSeries_pos_iff` — the singular series is positive exactly on
  the admissible gaps;
* `Brockian.SingularSeriesGaps13501360` — the resulting characterisation for the new gap
  range `1350 ≤ g ≤ 1360`, together with the exact value of the singular series for each
  admissible gap in that range.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Brockian

/-- A finite set `S ⊆ ℤ` is *admissible* if for every prime `p` some residue class mod `p`
is missed by `S`. -/

lemma not_admissible_gapSet_of_odd {g : ℕ} (hg : ¬ Even g) : ¬ Admissible (gapSet g) := by
  intro h
  obtain ⟨r, hr⟩ := h 2 Nat.prime_two
  have h0 : ((0 : ℤ) : ZMod 2) ≠ r := hr 0 (by simp [gapSet])
  have hgr : (((g : ℤ)) : ZMod 2) ≠ r := hr _ (by simp [gapSet])
  have hg0 : (((g : ℤ)) : ZMod 2) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdvd
    exact hg (even_iff_two_dvd.2 (by exact_mod_cast hdvd))
  rw [Int.cast_zero] at h0
  exact zmod_two_aux r _ h0 hgr hg0

/-- An even gap is admissible. -/
