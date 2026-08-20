/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- The gap pattern `(0, 1602, 1610)`, i.e. the triple of integer shifts
`{0, 1602, 1610}` (gaps `1602` and `1610` from the base point). -/
def gapSet16021610 : Finset ℤ := {0, 1602, 1610}

/--
**Admissibility of the gap range `(0, 1602, 1610)`.**

For every prime `p` there is a residue class mod `p` avoided by the triple
`{0, 1602, 1610}`; equivalently the triple does not cover all residues mod `p`
for any prime `p`, which is exactly the admissibility condition guaranteeing a
nonvanishing singular series `𝔖(H) ≠ 0` in the Hardy–Littlewood prime `k`-tuple
heuristic.
-/
theorem SingularSeriesGaps16021610 :
    ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ gapSet16021610, (h : ZMod p) ≠ r := by
  intro p hp
  by_cases hp5 : 5 ≤ p
  · haveI : NeZero p := ⟨hp.ne_zero⟩
    set S : Finset (ZMod p) :=
      {((0 : ℤ) : ZMod p), ((1602 : ℤ) : ZMod p), ((1610 : ℤ) : ZMod p)} with hS
    have hcard3 : S.card ≤ 3 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      have h2 : ({((1602 : ℤ) : ZMod p), ((1610 : ℤ) : ZMod p)} : Finset (ZMod p)).card ≤ 2 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        simp
      omega
    have hlt : S.card < Fintype.card (ZMod p) := by
      rw [ZMod.card]
      omega
    have hex : ∃ r : ZMod p, r ∉ S := by
      by_contra hcon
      push_neg at hcon
      have huniv : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hcon
      rw [huniv, Finset.card_univ] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨r, hr⟩ := hex
    refine ⟨r, ?_⟩
    intro h hh hcast
    apply hr
    simp only [gapSet16021610, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl <;> rw [← hcast] <;> simp [hS]
  · have h2 := hp.two_le
    interval_cases p
    · refine ⟨1, ?_⟩
      intro h hh
      simp only [gapSet16021610, Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl <;> decide
    · refine ⟨1, ?_⟩
      intro h hh
      simp only [gapSet16021610, Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl <;> decide
    · exact absurd hp (by norm_num)

/--
The same admissibility statement in classical (integer) form: for every prime `p`
there is an integer `r` such that no element of the gap range `{0, 1602, 1610}`
is congruent to `r` modulo `p`.
-/
theorem gapSet16021610_admissible :
    ∀ p : ℕ, p.Prime → ∃ r : ℤ, ∀ h ∈ gapSet16021610, ¬ ((p : ℤ) ∣ (h - r)) := by
  intro p hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨r0, hr0⟩ := SingularSeriesGaps16021610 p hp
  refine ⟨(r0.val : ℤ), ?_⟩
  intro h hh hdvd
  have hcast : ((h - (r0.val : ℤ) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
  have hEq : (h : ZMod p) = r0 := by
    push_cast at hcast
    simpa [sub_eq_zero] using hcast
  exact hr0 h hh hEq

/-- `nuP p` is `ν_p(H)`, the number of residue classes mod `p` occupied by the
gap range `H = {0, 1602, 1610}`. -/
def nuP (p : ℕ) : ℕ := (gapSet16021610.image (fun h : ℤ => (h : ZMod p))).card

/-- For every prime `p`, the gap range `{0, 1602, 1610}` occupies fewer than `p`
residue classes mod `p`. -/
theorem nuP_lt_of_prime (p : ℕ) (hp : p.Prime) : nuP p < p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨r, hr⟩ := SingularSeriesGaps16021610 p hp
  have hrmem : r ∉ gapSet16021610.image (fun h : ℤ => (h : ZMod p)) := by
    intro hmem
    obtain ⟨h, hh, hcast⟩ := Finset.mem_image.mp hmem
    exact hr h hh hcast
  have hss : gapSet16021610.image (fun h : ℤ => (h : ZMod p)) ⊂ Finset.univ := by
    refine Finset.ssubset_univ_iff.mpr ?_
    intro hEq
    exact hrmem (hEq ▸ Finset.mem_univ r)
  have := Finset.card_lt_card hss
  rwa [Finset.card_univ, ZMod.card] at this

/-- The local factor `1 - ν_p(H)/p` of the singular series of the gap range
`{0, 1602, 1610}` is strictly positive at every prime `p`; hence no factor of the
singular series vanishes. -/
theorem localFactor_pos_of_prime (p : ℕ) (hp : p.Prime) :
    0 < 1 - (nuP p : ℝ) / (p : ℝ) := by
  have hlt := nuP_lt_of_prime p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have : (nuP p : ℝ) / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    exact_mod_cast hlt
  linarith

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

