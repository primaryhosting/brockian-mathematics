/-
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; the identical module docstring follows the import.)

import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
Mathlib lemmas doing the real work here: `Finset.card_image_le` (bounds the local density
`ν_H(p)` by `|H|`), `ZMod.natCast_eq_zero_iff` (evens vanish mod `2`), and
`Finset.prod_pos` (positivity of the truncated Euler product).
-/

namespace Brockian

/-- The local density `ν_H(p)`: the number of residue classes modulo `p` occupied by the
shift set `H`.  This is the quantity appearing in each Euler factor of the Hardy–Littlewood
singular series of the tuple `H`. -/
def localDensity (H : Finset ℕ) (p : ℕ) : ℕ :=
  (H.image (fun h : ℕ => (h : ZMod p))).card

/-- A shift set `H` is *admissible* when, for every prime `p`, the members of `H` fail to
cover all residue classes modulo `p`. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → localDensity H p < p

/-- The truncated Hardy–Littlewood singular series of `H`, i.e. the product of the Euler
factors `(1 - ν_H(p)/p) / (1 - 1/p)^{|H|}` over primes `p ≤ N`. -/
noncomputable def singularSeriesPartial (H : Finset ℕ) (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
    (1 - (localDensity H p : ℝ) / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ H.card

lemma localDensity_le_card (H : Finset ℕ) (p : ℕ) : localDensity H p ≤ H.card :=
  Finset.card_image_le

lemma localDensity_lt_of_card_lt {H : Finset ℕ} {p : ℕ} (h : H.card < p) :
    localDensity H p < p :=
  lt_of_le_of_lt (localDensity_le_card H p) h

/-- Every Euler factor of an admissible tuple is strictly positive. -/
lemma euler_factor_pos {H : Finset ℕ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    0 < (1 - (localDensity H p : ℝ) / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ H.card := by
  have hp2 : (2 : ℕ) ≤ p := hp.two_le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hnum : 0 < 1 - (localDensity H p : ℝ) / (p : ℝ) := by
    have hlt : (localDensity H p : ℝ) < (p : ℝ) := by exact_mod_cast hH p hp
    have := (div_lt_one hp0).mpr hlt
    linarith
  have hden : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le <;> linarith
    linarith
  exact div_pos hnum (pow_pos hden _)

/-- The truncated singular series of an admissible tuple is strictly positive; in particular
it never vanishes, which is the local obstruction-free condition in the prime `k`-tuples
conjecture. -/
theorem singularSeriesPartial_pos {H : Finset ℕ} (hH : Admissible H) (N : ℕ) :
    0 < singularSeriesPartial H N := by
  refine Finset.prod_pos ?_
  intro p hp
  exact euler_factor_pos hH (Finset.mem_filter.mp hp).2

/-- Any pair of shifts differing by an even gap is admissible. -/
lemma admissible_pair_of_even {d : ℕ} (hd : Even d) : Admissible ({0, d} : Finset ℕ) := by
  intro p hp
  rcases eq_or_lt_of_le hp.two_le with h2 | h3
  · -- `p = 2`: both shifts are even, so only one residue class is occupied.
    subst h2
    have hd0 : ((d : ZMod 2)) = 0 := (ZMod.natCast_eq_zero_iff d 2).mpr hd.two_dvd
    have : localDensity ({0, d} : Finset ℕ) 2 = 1 := by
      simp [localDensity, hd0]
    omega
  · -- `p ≥ 3`: there are at most two shifts, hence at most two residue classes.
    have hcard : ({0, d} : Finset ℕ).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    exact lt_of_le_of_lt ((localDensity_le_card _ p).trans hcard) h3

/-- The explicit triple `{0, 1452, 1458}` is admissible. -/
lemma admissible_triple : Admissible ({0, 1452, 1458} : Finset ℕ) := by
  intro p hp
  by_cases h3 : 3 < p
  · have hcard : ({0, 1452, 1458} : Finset ℕ).card ≤ 3 := by decide
    exact lt_of_le_of_lt ((localDensity_le_card _ p).trans hcard) h3
  · interval_cases p
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · have : localDensity ({0, 1452, 1458} : Finset ℕ) 2 = 1 := by decide
      omega
    · have : localDensity ({0, 1452, 1458} : Finset ℕ) 3 = 1 := by decide
      omega

/-!
## Main result

A new admissible gap range around `1450–1460`:

* every even gap `d` in the range `1450 ≤ d ≤ 1460` yields an admissible pair `{0, d}`,
* the triple `{0, 1452, 1458}` of diameter `1458` inside that range is admissible,
* consequently all truncations of its Hardy–Littlewood singular series are strictly
  positive, so there is no local obstruction to infinitely many prime triples with these
  gaps.
-/
theorem SingularSeriesGaps14501460 :
    (∀ d ∈ Finset.Icc 1450 1460, Even d → Admissible ({0, d} : Finset ℕ)) ∧
      Admissible ({0, 1452, 1458} : Finset ℕ) ∧
      (∀ N : ℕ, 0 < singularSeriesPartial ({0, 1452, 1458} : Finset ℕ) N) ∧
      1458 ∈ Finset.Icc 1450 1460 := by
  refine ⟨fun d _ hd => admissible_pair_of_even hd, admissible_triple,
    fun N => singularSeriesPartial_pos admissible_triple N, by decide⟩

end Brockian

