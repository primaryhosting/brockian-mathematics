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

namespace Brockian

/-- A finite set of integers is **admissible** if for every prime `p` it misses at least one
residue class modulo `p` (equivalently, the local factor of the Hardy–Littlewood singular
series attached to the tuple is nonzero at every prime). -/
def Admissible (S : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ a ∈ S, (a : ZMod p) ≠ r

/-- The gap pair `{0, n}` is admissible exactly when the gap `n` is even. -/
theorem admissible_pair_iff (n : ℤ) : Admissible ({0, n} : Finset ℤ) ↔ Even n := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := h 2 Nat.prime_two
    have h0 : ((0 : ℤ) : ZMod 2) ≠ r := hr 0 (by simp)
    have hn : ((n : ℤ) : ZMod 2) ≠ r := hr n (by simp)
    have key : ∀ x y : ZMod 2, (0 : ZMod 2) ≠ y → x ≠ y → x = 0 := by decide
    have hz : ((n : ℤ) : ZMod 2) = 0 := key _ r (by simpa using h0) hn
    have hdvd : (2 : ℤ) ∣ n := by
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd n 2).mp hz
    obtain ⟨k, hk⟩ := hdvd
    exact ⟨k, by omega⟩
  · intro hn p hp
    have hdvd : (2 : ℤ) ∣ n := hn.two_dvd
    have hz2 : ((n : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd n 2).mpr (by simpa using hdvd)
    rcases eq_or_ne p 2 with rfl | hp2
    · refine ⟨1, ?_⟩
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · simp
      · rw [hz2]; decide
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨r, hr⟩ : ∃ r : ZMod p, r ∉ ({0, ((n : ℤ) : ZMod p)} : Finset (ZMod p)) := by
        by_contra hcon
        push_neg at hcon
        have hsub : (Finset.univ : Finset (ZMod p)) ⊆
            ({0, ((n : ℤ) : ZMod p)} : Finset (ZMod p)) := fun x _ => hcon x
        have hle := Finset.card_le_card hsub
        have h1 : (({0, ((n : ℤ) : ZMod p)} : Finset (ZMod p))).card ≤ 2 := by
          refine le_trans (Finset.card_insert_le _ _) ?_
          simp
        have h2 : (Finset.univ : Finset (ZMod p)).card = p := by
          simp [ZMod.card p]
        omega
      refine ⟨r, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      push_neg at hr
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact fun hc => hr.1 (by simpa using hc.symm)
      · exact fun hc => hr.2 hc.symm

/-- **New admissible gap ranges (1240–1250).** For every gap `n` in the range `1240 ≤ n ≤ 1250`,
the pair `{0, n}` is admissible — hence its Hardy–Littlewood singular series is nonvanishing —
precisely when `n` is even. (The range hypotheses `h1`, `h2` are part of the requested
statement; the equivalence in fact holds for every `n`, cf. `Brockian.admissible_pair_iff`.) -/
theorem SingularSeriesGaps12401250 (n : ℕ) (h1 : 1240 ≤ n) (h2 : n ≤ 1250) :
    Admissible ({0, (n : ℤ)} : Finset ℤ) ↔ Even n := by
  rw [admissible_pair_iff]
  exact Int.even_coe_nat n

/-- Explicitly: each even gap in the range 1240–1250 is admissible. -/
theorem admissible_even_gaps_1240_1250 (n : ℕ) (h1 : 1240 ≤ n) (h2 : n ≤ 1250) (hn : Even n) :
    Admissible ({0, (n : ℤ)} : Finset ℤ) :=
  (SingularSeriesGaps12401250 n h1 h2).mpr hn

/-- Sample instance of the new range: the gap 1246 is admissible. -/
theorem admissible_gap_1246 : Admissible ({0, (1246 : ℤ)} : Finset ℤ) :=
  admissible_even_gaps_1240_1250 1246 (by norm_num) (by norm_num) (by decide)

end Brockian

#print axioms Brockian.SingularSeriesGaps12401250
#print axioms Brockian.admissible_even_gaps_1240_1250
#print axioms Brockian.admissible_gap_1246

