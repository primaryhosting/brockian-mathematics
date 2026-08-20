import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

open Polynomial IntermediateField

namespace Math2

/-- A complex number is a *rational point* if it lies in the image of `ℚ`. -/

lemma phase1 : ∀ d k : ℕ, ∀ S : Finset ℂ, (∀ β ∈ S, IsIntegral ℚ β) →
    (∀ β ∈ S, deg β ≤ d) →
    (S.filter (fun β => deg β = d)).card ≤ k →
    ∃ f : ℚ[X], 0 < f.natDegree ∧ (∀ β ∈ S, IsRatPt (aeval β f)) ∧
      (∀ c : ℂ, aeval c (derivative f) = 0 → IsRatPt (aeval c f)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IHd =>
    intro k
    induction k with
    | zero =>
      intro S hint hS hcard
      rcases Nat.lt_or_ge d 2 with hd | hd
      · exact phase1_trivial S hint (fun β hβ => by have := hS β hβ; omega)
      · refine IHd (d - 1) (by omega) S.card S hint (fun β hβ => ?_) (Finset.card_filter_le _ _)
        have h1 := hS β hβ
        have h2 : deg β ≠ d := by
          intro he
          have hmem : β ∈ S.filter (fun β => deg β = d) := Finset.mem_filter.2 ⟨hβ, he⟩
          rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)] at hmem
          simp at hmem
        omega
    | succ k IHk =>
      intro S hint hS hcard
      rcases le_or_gt (S.filter (fun β => deg β = d)).card k with hsmall | hbig
      · exact IHk S hint hS hsmall
      rcases Nat.lt_or_ge d 2 with hd | hd
      · exact phase1_trivial S hint (fun β hβ => by have := hS β hβ; omega)
      obtain ⟨α, hα⟩ : (S.filter (fun β => deg β = d)).Nonempty :=
        Finset.card_pos.1 (by omega)
      obtain ⟨hαS, hαd⟩ := Finset.mem_filter.1 hα
      set p : ℚ[X] := minpoly ℚ α with hp
      have hpdeg : p.natDegree = d := hαd
      have hderiv0 : derivative p ≠ 0 := by
        intro hc
        have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hc
        omega
      set crit : Finset ℂ := ((derivative p).aroots ℂ).toFinset with hcrit
      set S' : Finset ℂ :=
        S.image (fun β => aeval β p) ∪ crit.image (fun c => aeval c p) with hS'def
      have hcritlt : ∀ c ∈ crit, deg (aeval c p) < d := by
        intro c hc
        rw [hcrit, Multiset.mem_toFinset, mem_aroots] at hc
        have hcint : IsIntegral ℚ c := isIntegral_of_aeval_eq_zero hderiv0 hc.2
        have h1 : deg c ≤ (derivative p).natDegree := deg_le_of_aeval_eq_zero hderiv0 hc.2
        have h2 : (derivative p).natDegree < p.natDegree := natDegree_derivative_lt (by omega)
        calc deg (aeval c p) ≤ deg c := deg_aeval_le hcint p
          _ ≤ (derivative p).natDegree := h1
          _ < d := by omega
      have hαimg : aeval α p = 0 := minpoly.aeval ℚ α
      have hbound : ∀ γ ∈ S', deg γ ≤ d := by
        intro γ hγ
        rw [hS'def, Finset.mem_union] at hγ
        rcases hγ with hγ | hγ
        · obtain ⟨β, hβS, rfl⟩ := Finset.mem_image.1 hγ
          exact (deg_aeval_le (hint β hβS) p).trans (hS β hβS)
        · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
          exact le_of_lt (hcritlt c hc)
      have hsub : S'.filter (fun γ => deg γ = d) ⊆
          ((S.filter (fun β => deg β = d)).erase α).image (fun β => aeval β p) := by
        intro γ hγ
        obtain ⟨hγS', hγd⟩ := Finset.mem_filter.1 hγ
        rw [hS'def, Finset.mem_union] at hγS'
        rcases hγS' with hγ1 | hγ1
        · obtain ⟨β, hβS, hβγ⟩ := Finset.mem_image.1 hγ1
          have hdβ : deg β = d := by
            have h1 : deg γ ≤ deg β := by rw [← hβγ]; exact deg_aeval_le (hint β hβS) p
            have := hS β hβS
            omega
          have hβα : β ≠ α := by
            rintro rfl
            rw [hαimg] at hβγ
            rw [← hβγ, deg_zero] at hγd
            omega
          exact Finset.mem_image.2 ⟨β, Finset.mem_erase.2 ⟨hβα, Finset.mem_filter.2 ⟨hβS, hdβ⟩⟩,
            hβγ⟩
        · obtain ⟨c, hc, hcγ⟩ := Finset.mem_image.1 hγ1
          exact absurd hγd (by rw [← hcγ]; exact Nat.ne_of_lt (hcritlt c hc))
      have hcount : (S'.filter (fun γ => deg γ = d)).card ≤ k := by
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_image_le (s := (S.filter (fun β => deg β = d)).erase α)
          (f := fun β => aeval β p)
        have h3 : ((S.filter (fun β => deg β = d)).erase α).card =
            (S.filter (fun β => deg β = d)).card - 1 := Finset.card_erase_of_mem hα
        omega
      have hint' : ∀ γ ∈ S', IsIntegral ℚ γ := by
        intro γ hγ
        rw [hS'def, Finset.mem_union] at hγ
        rcases hγ with hγ | hγ
        · obtain ⟨β, hβS, rfl⟩ := Finset.mem_image.1 hγ
          exact isIntegral_aeval (hint β hβS) p
        · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
          rw [hcrit, Multiset.mem_toFinset, mem_aroots] at hc
          exact isIntegral_aeval (isIntegral_of_aeval_eq_zero hderiv0 hc.2) p
      obtain ⟨g, hg1, hg2, hg3⟩ := IHk S' hint' hbound hcount
      have hpS' : ∀ β ∈ S, aeval β p ∈ S' := fun β hβ =>
        Finset.mem_union_left _ (Finset.mem_image.2 ⟨β, hβ, rfl⟩)
      refine ⟨g.comp p, ?_, ?_, ?_⟩
      · rw [natDegree_comp]
        exact Nat.mul_pos hg1 (by omega)
      · intro β hβ
        rw [aeval_comp]
        exact hg2 _ (hpS' β hβ)
      · intro c hc
        rw [aeval_comp]
        rcases critval_comp hc with h1 | h1
        · refine hg2 _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨c, ?_, rfl⟩))
          rw [hcrit, Multiset.mem_toFinset, mem_aroots]
          exact ⟨hderiv0, h1⟩
        · exact hg3 _ h1

