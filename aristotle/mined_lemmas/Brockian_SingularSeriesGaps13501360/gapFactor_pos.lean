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

lemma gapFactor_pos (g : ℕ) : 0 < gapFactor g := by
  refine Finset.prod_pos ?_
  intro p hp
  have h3 : 3 ≤ p := three_le_of_mem_erase_two hp
  have h3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  positivity

/-- An odd gap is never admissible: the pattern `{0, g}` covers both residues mod `2`. -/
