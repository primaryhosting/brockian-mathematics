/-
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Belyi Theorem

Category: Frontier Math
Target: `Math2.belyi_theorem`
Provenance: Aristotle theorem prover (Harmonic)

## Contents

This file formalizes Belyi's theorem for the projective line with marked points, i.e. for the
curves `ℙ¹ \ S` where `S` is a finite set of points: such a marked curve is defined over `ℚ̄`
(all points of `S` are algebraic numbers) if and only if there is a Belyi map, i.e. a nonconstant
map `ℙ¹ → ℙ¹` defined over `ℚ` which is ramified only above `{0, 1, ∞}` and which sends `S`
into `{0, 1, ∞}`.

Belyi maps are realized here by polynomials `f ∈ ℚ[X]`; such an `f`, viewed as a self-map of
`ℙ¹`, sends `∞` to `∞`, so ramification above `∞` is automatic and the condition on the
ramification is that all *finite* critical values lie in `{0, 1}`.  This is `Math2.IsBelyi`.

The main result is `Math2.belyi_theorem`.  The non-trivial direction is Belyi's construction,
which is carried out in two steps:

* `Math2.rationalize`: composing with a suitable polynomial over `ℚ` one can force all critical
  values to be rational.  This is the induction on the degrees over `ℚ` of the critical values,
  using that composing with the minimal polynomial of a critical value of maximal degree `D`
  strictly decreases the number of critical values of degree `D`.
* `Math2.rat_reduction`: any finite set of *rational* points can be pushed into `{0, 1}` by a
  Belyi polynomial.  This is Belyi's classical argument with the polynomials
  `x ↦ c · x ^ a (1 - x) ^ n` (`Math2.belyiP`), which have all their critical values in `{0, 1}`
  and collapse `{0, 1, a / (a + n)}` into `{0, 1}`, combined with affine normalizations.
-/

open Polynomial

set_option maxHeartbeats 1000000

namespace Math2

noncomputable section

/-- The degree over `ℚ` of a complex number (`0` if transcendental). -/

lemma rationalize_aux (D : ℕ) : ∀ N : ℕ, ∀ f : ℚ[X], 0 < f.natDegree →
    (∀ w ∈ critF f, algDeg w ≤ D) →
    ((critF f).filter (fun w => algDeg w = D)).card ≤ N →
    ∃ g : ℚ[X], 0 < g.natDegree ∧
      ∀ w ∈ critF (g.comp f), ∃ q : ℚ, algebraMap ℚ ℂ q = w := by
  induction D using Nat.strong_induction_on with
  | _ D ihD =>
  by_cases hD1 : D ≤ 1
  · intro _ f hf hDf _
    refine ⟨X, by simp, ?_⟩
    intro w hw
    rw [Polynomial.X_comp] at hw
    exact rat_of_algDeg_le_one (isIntegral_of_mem_critF hf hw) (le_trans (hDf w hw) hD1)
  · intro N
    induction N with
    | zero =>
      intro f hf hDf hN
      by_cases hex : ∃ b ∈ critF f, algDeg b = D
      · obtain ⟨b, hb, hbD⟩ := hex
        exfalso
        have : b ∈ (critF f).filter (fun w => algDeg w = D) := Finset.mem_filter.2 ⟨hb, hbD⟩
        have := Finset.card_pos.2 ⟨b, this⟩
        omega
      · refine ihD (D - 1) (by omega) ((critF f).card) f hf ?_ (Finset.card_filter_le _ _)
        intro w hw
        have h1 := hDf w hw
        have h2 : algDeg w ≠ D := fun h => hex ⟨w, hw, h⟩
        omega
    | succ N ihN =>
      intro f hf hDf hN
      by_cases hex : ∃ b ∈ critF f, algDeg b = D
      · obtain ⟨b, hb, hbD⟩ := hex
        have hbint : IsIntegral ℚ b := isIntegral_of_mem_critF hf hb
        have hpdeg : (minpoly ℚ b).natDegree = D := hbD
        have hppos : 0 < (minpoly ℚ b).natDegree := by omega
        have hpf : 0 < ((minpoly ℚ b).comp f).natDegree := by
          rw [Polynomial.natDegree_comp]; exact Nat.mul_pos hppos hf
        have hbp : aeval b (minpoly ℚ b) = 0 := minpoly.aeval ℚ b
        have hzero : algDeg (0 : ℂ) = 1 := by simp [algDeg, minpoly.zero]
        have hcritp : ∀ w ∈ critF (minpoly ℚ b), algDeg w < D := by
          intro w hw
          have := algDeg_critF_lt hppos hw
          omega
        have hdegs : ∀ w ∈ critF ((minpoly ℚ b).comp f), algDeg w ≤ D := by
          intro w hw
          rcases Finset.mem_union.1 (critF_comp_subset hppos hf hw) with h | h
          · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
            exact le_trans (algDeg_aeval_le _ (isIntegral_of_mem_critF hf ht)) (hDf t ht)
          · exact le_of_lt (hcritp w h)
        have hbfilter : b ∈ (critF f).filter (fun w => algDeg w = D) :=
          Finset.mem_filter.2 ⟨hb, hbD⟩
        have hcnt : ((critF ((minpoly ℚ b).comp f)).filter (fun w => algDeg w = D)).card ≤ N := by
          have hsub : (critF ((minpoly ℚ b).comp f)).filter (fun w => algDeg w = D) ⊆
              (((critF f).filter (fun w => algDeg w = D)).erase b).image
                (fun t => aeval t (minpoly ℚ b)) := by
            intro w hw
            obtain ⟨hw1, hw2⟩ := Finset.mem_filter.1 hw
            rcases Finset.mem_union.1 (critF_comp_subset hppos hf hw1) with h | h
            · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
              have htD : algDeg t = D := by
                have h1 := algDeg_aeval_le (minpoly ℚ b) (isIntegral_of_mem_critF hf ht)
                have h2 := hDf t ht
                omega
              have htb : t ≠ b := by
                intro hcon
                rw [hcon, hbp, hzero] at hw2
                omega
              exact Finset.mem_image.2
                ⟨t, Finset.mem_erase.2 ⟨htb, Finset.mem_filter.2 ⟨ht, htD⟩⟩, rfl⟩
            · exact absurd hw2 (Nat.ne_of_lt (hcritp w h))
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_image_le
            (s := ((critF f).filter (fun w => algDeg w = D)).erase b)
            (f := fun t => aeval t (minpoly ℚ b))
          have h3 : (((critF f).filter (fun w => algDeg w = D)).erase b).card
              = ((critF f).filter (fun w => algDeg w = D)).card - 1 :=
            Finset.card_erase_of_mem hbfilter
          have h4 : 1 ≤ ((critF f).filter (fun w => algDeg w = D)).card :=
            Finset.card_pos.2 ⟨b, hbfilter⟩
          omega
        obtain ⟨g', hg'pos, hg'⟩ := ihN ((minpoly ℚ b).comp f) hpf hdegs hcnt
        refine ⟨g'.comp (minpoly ℚ b), ?_, ?_⟩
        · rw [Polynomial.natDegree_comp]; exact Nat.mul_pos hg'pos hppos
        · intro w hw
          rw [Polynomial.comp_assoc] at hw
          exact hg' w hw
      · refine ihD (D - 1) (by omega) ((critF f).card) f hf ?_ (Finset.card_filter_le _ _)
        intro w hw
        have h1 := hDf w hw
        have h2 : algDeg w ≠ D := fun h => hex ⟨w, hw, h⟩
        omega

/-- For any nonconstant `f ∈ ℚ[X]` there is a nonconstant `g ∈ ℚ[X]` such that all critical
values of `g ∘ f` are rational. -/
