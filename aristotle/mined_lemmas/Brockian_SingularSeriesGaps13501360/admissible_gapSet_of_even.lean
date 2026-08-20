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

lemma admissible_gapSet_of_even {g : ℕ} (hg : Even g) : Admissible (gapSet g) := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨1, ?_⟩
    intro s hs
    have hgz : (((g : ℤ)) : ZMod 2) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast even_iff_two_dvd.1 hg
    simp only [gapSet, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rw [Int.cast_zero]; exact zero_ne_one
    · rw [hgz]; exact zero_ne_one
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (ZMod p)) ⊆
        (gapSet g).image (fun s : ℤ => (s : ZMod p)) := by
      intro r _
      obtain ⟨s, hs, hsr⟩ := hcon r
      exact Finset.mem_image.2 ⟨s, hs, hsr⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card] at hcard
    have h2 : ((gapSet g).image (fun s : ℤ => (s : ZMod p))).card ≤ 2 :=
      le_trans (Finset.card_image_le)
        (le_trans (Finset.card_insert_le _ _) (by simp))
    omega

/-- **Admissibility of a gap.** The pattern `{0, g}` is admissible exactly when `g` is even. -/
