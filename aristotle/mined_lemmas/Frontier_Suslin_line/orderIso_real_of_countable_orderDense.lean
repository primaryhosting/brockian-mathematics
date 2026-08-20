import Mathlib
import RequestProject.CantorDedekind

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open TopologicalSpace Set

namespace Frontier

/-- The **countable chain condition** (ccc) for a topological space `X`: every family of
pairwise disjoint nonempty open subsets of `X` is countable. -/

theorem orderIso_real_of_countable_orderDense (D : Set X) (hDc : D.Countable)
    (hD : ∀ a b : X, a < b → ∃ d ∈ D, a < d ∧ d < b) : Nonempty (X ≃o ℝ) := by
  -- `D`, as a linear order, is a countable dense order without endpoints, hence `≃o ℚ`.
  haveI : Countable (↥D) := hDc.to_subtype
  haveI : Nonempty (↥D) := by
    obtain ⟨a⟩ := ‹Nonempty X›
    obtain ⟨b, hb⟩ := exists_gt a
    obtain ⟨d, hdD, _, _⟩ := hD a b hb
    exact ⟨⟨d, hdD⟩⟩
  haveI : DenselyOrdered (↥D) := by
    refine ⟨fun a b hab => ?_⟩
    obtain ⟨d, hdD, h1, h2⟩ := hD a b hab
    exact ⟨⟨d, hdD⟩, h1, h2⟩
  haveI : NoMinOrder (↥D) := by
    refine ⟨fun a => ?_⟩
    obtain ⟨y, hy⟩ := exists_lt (a : X)
    obtain ⟨d, hdD, _, h2⟩ := hD y a hy
    exact ⟨⟨d, hdD⟩, h2⟩
  haveI : NoMaxOrder (↥D) := by
    refine ⟨fun a => ?_⟩
    obtain ⟨y, hy⟩ := exists_gt (a : X)
    obtain ⟨d, hdD, h1, _⟩ := hD a y hy
    exact ⟨⟨d, hdD⟩, h1⟩
  obtain ⟨g⟩ := Order.iso_of_countable_dense (↥D) ℚ
  -- the embedding of `X` into `ℝ`
  set q : ↥D → ℝ := fun d => ((g d : ℚ) : ℝ) with hq
  set S : X → Set ℝ := fun x => q '' {d : ↥D | (d : X) < x} with hS
  have hqmono : StrictMono q := by
    intro a b hab
    have h : g a < g b := g.lt_iff_lt.mpr hab
    simp only [hq]
    exact_mod_cast h
  have hne : ∀ x : X, (S x).Nonempty := by
    intro x
    obtain ⟨y, hy⟩ := exists_lt x
    obtain ⟨d, hdD, _, h2⟩ := hD y x hy
    exact ⟨q ⟨d, hdD⟩, ⟨d, hdD⟩, h2, rfl⟩
  have hbdd : ∀ x : X, BddAbove (S x) := by
    intro x
    obtain ⟨z, hz⟩ := exists_gt x
    obtain ⟨d, hdD, h1, _⟩ := hD x z hz
    refine ⟨q ⟨d, hdD⟩, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    have : e < (⟨d, hdD⟩ : ↥D) := Subtype.coe_lt_coe.mp (lt_trans he h1)
    exact (hqmono this).le
  set F : X → ℝ := fun x => sSup (S x) with hF
  have hle : ∀ (x : X) (d : ↥D), (d : X) < x → q d ≤ F x := by
    intro x d hd
    exact le_csSup (hbdd x) ⟨d, hd, rfl⟩
  have hFmono : StrictMono F := by
    intro a b hab
    obtain ⟨d₁, hd₁D, ha1, h1b⟩ := hD a b hab
    obtain ⟨d₂, hd₂D, h12, h2b⟩ := hD d₁ b h1b
    have hFa : F a ≤ q ⟨d₁, hd₁D⟩ := by
      refine csSup_le (hne a) ?_
      rintro _ ⟨e, he, rfl⟩
      exact (hqmono (Subtype.coe_lt_coe.mp (lt_trans he ha1) :
        e < (⟨d₁, hd₁D⟩ : ↥D))).le
    have h2 : q ⟨d₂, hd₂D⟩ ≤ F b := hle b ⟨d₂, hd₂D⟩ h2b
    have : q ⟨d₁, hd₁D⟩ < q ⟨d₂, hd₂D⟩ := hqmono h12
    linarith
  have hFsurj : Function.Surjective F := by
    intro r
    set T : Set X := (fun d : ↥D => (d : X)) '' {d : ↥D | q d < r} with hT
    have hTne : T.Nonempty := by
      obtain ⟨s, hs⟩ := exists_rat_lt r
      exact ⟨(g.symm s : X), ⟨g.symm s, by simp [hq, hs], rfl⟩⟩
    have hTbdd : BddAbove T := by
      obtain ⟨s, hs⟩ := exists_rat_gt r
      refine ⟨(g.symm s : X), ?_⟩
      rintro _ ⟨e, he, rfl⟩
      have hlt : q e < ((s : ℚ) : ℝ) := lt_trans he hs
      simp only [hq] at hlt
      have hgs : g e < s := by exact_mod_cast hlt
      have : e < g.symm s := by
        have h := (g.lt_iff_lt (x := e) (y := g.symm s))
        simpa using h.mp (by simpa using hgs)
      exact Subtype.coe_le_coe.mpr this.le
    refine ⟨sSup T, le_antisymm ?_ ?_⟩
    · -- `F (sSup T) ≤ r`
      refine csSup_le (hne _) ?_
      rintro _ ⟨e, he, rfl⟩
      obtain ⟨y, hyT, hy⟩ := exists_lt_of_lt_csSup hTne he
      obtain ⟨d, hd, rfl⟩ := hyT
      have : e < d := hy
      exact le_of_lt (lt_trans (hqmono this) hd)
    · -- `r ≤ F (sSup T)`
      by_contra hcon
      push_neg at hcon
      obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hcon
      obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn hs2
      have hst : (g.symm s : X) < (g.symm t : X) := by
        have : g.symm s < g.symm t := by
          have hst' : s < t := by exact_mod_cast ht1
          simpa using (g.symm.lt_iff_lt (x := s) (y := t)).mpr hst'
        exact this
      have hts : (g.symm t : X) ≤ sSup T := by
        refine le_csSup hTbdd ⟨g.symm t, ?_, rfl⟩
        simp only [mem_setOf_eq, hq]
        simpa using ht2
      have hlt : (g.symm s : X) < sSup T := lt_of_lt_of_le hst hts
      have := hle (sSup T) (g.symm s) hlt
      have hqs : q (g.symm s) = ((s : ℚ) : ℝ) := by simp [hq]
      rw [hqs] at this
      linarith
  exact ⟨StrictMono.orderIsoOfSurjective F hFmono hFsurj⟩

/-- A nonempty conditionally complete dense linear order without endpoints whose order topology
is separable is order-isomorphic to `ℝ`. -/
