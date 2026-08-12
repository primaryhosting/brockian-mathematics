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
def Admissible (S : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ s ∈ S, (s : ZMod p) ≠ r

/-- The two–element pattern `{0, g}` describing a prime pair with gap `g`. -/
def gapSet (g : ℕ) : Finset ℤ := {0, (g : ℤ)}

/-- The arithmetic factor `∏_{p ∣ g, p odd} (p-1)/(p-2)` of the singular series. -/
noncomputable def gapFactor (g : ℕ) : ℝ :=
  ∏ p ∈ g.primeFactors.erase 2, ((p : ℝ) - 1) / ((p : ℝ) - 2)

/-- The normalised Hardy–Littlewood singular series `𝔖(g) / (2 C₂)` for the prime pair
pattern `{0, g}`. -/
noncomputable def normalizedSingularSeries (g : ℕ) : ℝ :=
  if Even g then gapFactor g else 0

/-- Every prime dividing `g` other than `2` is at least `3`. -/
lemma three_le_of_mem_erase_two {g p : ℕ} (hp : p ∈ g.primeFactors.erase 2) : 3 ≤ p := by
  have hp2 : p ≠ 2 := Finset.ne_of_mem_erase hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  have := hprime.two_le
  omega

/-- `ZMod 2` has only two elements, so three pairwise distinct values cannot exist. -/
private lemma zmod_two_aux : ∀ r a : ZMod 2, (0 : ZMod 2) ≠ r → a ≠ r → a ≠ 0 → False := by
  decide

/-- The arithmetic factor is strictly positive. -/
lemma gapFactor_pos (g : ℕ) : 0 < gapFactor g := by
  refine Finset.prod_pos ?_
  intro p hp
  have h3 : 3 ≤ p := three_le_of_mem_erase_two hp
  have h3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  positivity

/-- An odd gap is never admissible: the pattern `{0, g}` covers both residues mod `2`. -/
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
theorem admissible_gapSet_iff (g : ℕ) : Admissible (gapSet g) ↔ Even g := by
  constructor
  · intro h
    by_contra hg
    exact not_admissible_gapSet_of_odd hg h
  · exact admissible_gapSet_of_even

/-- The singular series is positive exactly on the admissible gaps. -/
theorem normalizedSingularSeries_pos_iff (g : ℕ) :
    0 < normalizedSingularSeries g ↔ Admissible (gapSet g) := by
  rw [admissible_gapSet_iff, normalizedSingularSeries]
  by_cases hg : Even g <;> simp [hg, gapFactor_pos g]

lemma primeFactors_1350 : Nat.primeFactors 1350 = {2, 3, 5} := by
  rw [show (1350 : ℕ) = 2 * (3 ^ 3 * 5 ^ 2) from by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_pow _ (by norm_num), Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]
  rfl

lemma primeFactors_1352 : Nat.primeFactors 1352 = {2, 13} := by
  rw [show (1352 : ℕ) = 2 ^ 3 * 13 ^ 2 from by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_pow _ (by norm_num), Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  rfl

lemma primeFactors_1354 : Nat.primeFactors 1354 = {2, 677} := by
  rw [show (1354 : ℕ) = 2 * 677 from by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  rfl

lemma primeFactors_1356 : Nat.primeFactors 1356 = {2, 3, 113} := by
  rw [show (1356 : ℕ) = 2 ^ 2 * (3 * 113) from by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]
  rfl

lemma primeFactors_1358 : Nat.primeFactors 1358 = {2, 7, 97} := by
  rw [show (1358 : ℕ) = 2 * (7 * 97) from by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]
  rfl

lemma primeFactors_1360 : Nat.primeFactors 1360 = {2, 5, 17} := by
  rw [show (1360 : ℕ) = 2 ^ 4 * (5 * 17) from by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]
  rfl

theorem normalizedSingularSeries_1350 : normalizedSingularSeries 1350 = 8 / 3 := by
  rw [normalizedSingularSeries, if_pos (by decide), gapFactor, primeFactors_1350]
  norm_num [show ({2, 3, 5} : Finset ℕ).erase 2 = {3, 5} from by rfl]

theorem normalizedSingularSeries_1352 : normalizedSingularSeries 1352 = 12 / 11 := by
  rw [normalizedSingularSeries, if_pos (by decide), gapFactor, primeFactors_1352]
  norm_num [show ({2, 13} : Finset ℕ).erase 2 = {13} from by rfl]

theorem normalizedSingularSeries_1354 : normalizedSingularSeries 1354 = 676 / 675 := by
  rw [normalizedSingularSeries, if_pos (by decide), gapFactor, primeFactors_1354]
  norm_num [show ({2, 677} : Finset ℕ).erase 2 = {677} from by rfl]

theorem normalizedSingularSeries_1356 : normalizedSingularSeries 1356 = 224 / 111 := by
  rw [normalizedSingularSeries, if_pos (by decide), gapFactor, primeFactors_1356]
  norm_num [show ({2, 3, 113} : Finset ℕ).erase 2 = {3, 113} from by rfl]

theorem normalizedSingularSeries_1358 : normalizedSingularSeries 1358 = 576 / 475 := by
  rw [normalizedSingularSeries, if_pos (by decide), gapFactor, primeFactors_1358]
  norm_num [show ({2, 7, 97} : Finset ℕ).erase 2 = {7, 97} from by rfl]

theorem normalizedSingularSeries_1360 : normalizedSingularSeries 1360 = 64 / 45 := by
  rw [normalizedSingularSeries, if_pos (by decide), gapFactor, primeFactors_1360]
  norm_num [show ({2, 5, 17} : Finset ℕ).erase 2 = {5, 17} from by rfl]

/-- **New admissible gap range `1350 ≤ g ≤ 1360`.**

For every gap `g` in this range the pattern `{0, g}` is admissible iff `g` is even, iff the
Hardy–Littlewood singular series `𝔖(g)` is positive; and for each of the six admissible
gaps in the range the normalised singular series `𝔖(g)/(2C₂)` takes the stated value. -/
theorem SingularSeriesGaps13501360 :
    (∀ g : ℕ, 1350 ≤ g → g ≤ 1360 →
        ((Admissible (gapSet g) ↔ Even g) ∧
         (0 < normalizedSingularSeries g ↔ Even g))) ∧
      normalizedSingularSeries 1350 = 8 / 3 ∧
      normalizedSingularSeries 1352 = 12 / 11 ∧
      normalizedSingularSeries 1354 = 676 / 675 ∧
      normalizedSingularSeries 1356 = 224 / 111 ∧
      normalizedSingularSeries 1358 = 576 / 475 ∧
      normalizedSingularSeries 1360 = 64 / 45 := by
  refine ⟨fun g _ _ => ⟨admissible_gapSet_iff g, ?_⟩, normalizedSingularSeries_1350,
    normalizedSingularSeries_1352, normalizedSingularSeries_1354,
    normalizedSingularSeries_1356, normalizedSingularSeries_1358,
    normalizedSingularSeries_1360⟩
  rw [normalizedSingularSeries_pos_iff, admissible_gapSet_iff]

end Brockian

import Mathlib
import RequestProject.SingularSeriesGaps

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

