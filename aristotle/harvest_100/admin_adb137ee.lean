/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

open Finset

/-- A finite set of integers is *admissible* if, for every prime `p`, it fails to cover
all residue classes modulo `p`.  This is exactly the condition under which the
Hardy–Littlewood singular series of the tuple is nonzero. -/
def Admissible (S : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ s ∈ S, (s : ZMod p) ≠ r

/-- The odd part of the Hardy–Littlewood singular series for the prime pair `(n, n + d)`:
`∏_{p ∣ d, p odd} (p - 1) / (p - 2)`, extended by `0` at inadmissible gaps `d`
(that is, at `d = 0` and at odd `d`).  The universal factor `2 C₂` is omitted. -/
noncomputable def singularSeriesFactor (d : ℤ) : ℝ :=
  if Even d ∧ d ≠ 0 then
    ∏ p ∈ d.natAbs.primeFactors.erase 2, ((p : ℝ) - 1) / ((p : ℝ) - 2)
  else 0

section Basic

/-- Pigeonhole: a set with fewer than `p` elements misses a residue class mod `p`. -/
lemma exists_missing_residue (S : Finset ℤ) (p : ℕ) (hp : p.Prime) (h : S.card < p) :
    ∃ r : ZMod p, ∀ s ∈ S, (s : ZMod p) ≠ r := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set T := S.image (fun s : ℤ => (s : ZMod p)) with hT
  have hcard : T.card < Fintype.card (ZMod p) := by
    have hle : T.card ≤ S.card := Finset.card_image_le
    simpa [ZMod.card p] using lt_of_le_of_lt hle h
  obtain ⟨r, hr⟩ : ∃ r : ZMod p, r ∉ T := by
    by_contra hc
    push_neg at hc
    have hu : T = Finset.univ := Finset.eq_univ_iff_forall.mpr hc
    rw [hu, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  exact ⟨r, fun s hs hsr => hr (by rw [hT]; exact Finset.mem_image.mpr ⟨s, hs, hsr⟩)⟩

/-- A gap `d` is admissible (as the pair `{0, d}`) exactly when `d` is even and nonzero. -/
theorem admissible_pair_iff (d : ℤ) (hd : d ≠ 0) :
    Admissible {0, d} ↔ Even d := by
  have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  constructor
  · intro h
    obtain ⟨r, hr⟩ := h 2 Nat.prime_two
    have h0 : ((0 : ℤ) : ZMod 2) ≠ r := hr 0 (by simp)
    have h1 : ((d : ℤ) : ZMod 2) ≠ r := hr d (by simp)
    simp only [Int.cast_zero] at h0
    have hr1 : r = 1 := by
      rcases hcases r with h | h
      · exact absurd h.symm h0
      · exact h
    subst hr1
    have hd0 : (d : ZMod 2) = 0 := by
      rcases hcases ((d : ℤ) : ZMod 2) with h | h
      · exact h
      · exact absurd h h1
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd d 2).mp hd0
    exact ⟨k, by omega⟩
  · intro hev p hp
    rcases eq_or_ne p 2 with rfl | hp2
    · refine ⟨1, ?_⟩
      intro s hs
      have hs0 : (s : ZMod 2) = 0 := by
        rcases Finset.mem_insert.mp hs with h | h
        · rw [h]; simp
        · have hs' : s = d := by simpa using h
          rw [hs']
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd d 2).mpr hev.two_dvd
      rw [hs0]
      decide
    · have hcard : ({0, d} : Finset ℤ).card < p := by
        have h2 : ({0, d} : Finset ℤ).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
        have hlt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
        omega
      exact exists_missing_residue _ p hp hcard

/-- The singular series factor is positive at even nonzero gaps. -/
theorem singularSeriesFactor_pos_of_even {d : ℤ} (hev : Even d) (hd : d ≠ 0) :
    0 < singularSeriesFactor d := by
  rw [singularSeriesFactor, if_pos ⟨hev, hd⟩]
  refine Finset.prod_pos ?_
  intro p hp
  have hp2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hp).2
  have h3 : 3 ≤ p := by
    rcases hpp.two_le.lt_or_eq with h | h
    · omega
    · omega
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
    linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
    linarith
  positivity

/-- The singular series factor vanishes at inadmissible gaps. -/
theorem singularSeriesFactor_eq_zero_of_odd {d : ℤ} (hodd : ¬ Even d) :
    singularSeriesFactor d = 0 := by
  rw [singularSeriesFactor, if_neg]
  exact fun h => hodd h.1

/-- Positivity of the singular series factor characterises admissible gaps. -/
theorem singularSeriesFactor_pos_iff_admissible (d : ℤ) (hd : d ≠ 0) :
    0 < singularSeriesFactor d ↔ Admissible {0, d} := by
  rw [admissible_pair_iff d hd]
  constructor
  · intro h
    by_contra hodd
    rw [singularSeriesFactor_eq_zero_of_odd hodd] at h
    exact lt_irrefl _ h
  · intro hev
    exact singularSeriesFactor_pos_of_even hev hd

end Basic

/-- **Singular series gaps in the range 1350–1360.**
For every gap `d` in the range `1350 ≤ d ≤ 1360`, the pair `{0, d}` is admissible – equivalently,
the singular series factor `𝔖(d)` is positive – precisely when `d` is even; and for odd `d`
in this range the pair is inadmissible and the singular series factor vanishes.
The admissible gaps in this range are therefore exactly
`1350, 1352, 1354, 1356, 1358, 1360`. -/
theorem SingularSeriesGaps13501360 :
    (∀ d : ℤ, 1350 ≤ d → d ≤ 1360 →
        ((Admissible {0, d} ↔ Even d) ∧ (0 < singularSeriesFactor d ↔ Even d))) ∧
    (∀ d ∈ ({1350, 1352, 1354, 1356, 1358, 1360} : Finset ℤ),
        Admissible {0, d} ∧ 0 < singularSeriesFactor d) ∧
    (∀ d ∈ ({1351, 1353, 1355, 1357, 1359} : Finset ℤ),
        ¬ Admissible {0, d} ∧ singularSeriesFactor d = 0) := by
  have key : ∀ d : ℤ, 1350 ≤ d → d ≤ 1360 →
      ((Admissible {0, d} ↔ Even d) ∧ (0 < singularSeriesFactor d ↔ Even d)) := by
    intro d hd1 _
    have hd : d ≠ 0 := by omega
    refine ⟨admissible_pair_iff d hd, ?_⟩
    rw [singularSeriesFactor_pos_iff_admissible d hd, admissible_pair_iff d hd]
  refine ⟨key, ?_, ?_⟩
  · intro d hd
    fin_cases hd <;>
      exact ⟨((key _ (by norm_num) (by norm_num)).1).mpr (by norm_num),
        ((key _ (by norm_num) (by norm_num)).2).mpr (by norm_num)⟩
  · intro d hd
    fin_cases hd <;>
      exact ⟨fun hA => by
          have h := ((key _ (by norm_num) (by norm_num)).1).mp hA
          norm_num at h,
        singularSeriesFactor_eq_zero_of_odd (by norm_num)⟩

end Brockian

import Mathlib

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

