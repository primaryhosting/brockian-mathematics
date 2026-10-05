import Mathlib
/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Basic notions -/

/-- The set of critical values in `ℂ` of a polynomial with rational coefficients.
Viewing `f ∈ ℚ[X]` as a morphism `ℙ¹ → ℙ¹`, these are the finite branch points of `f`. -/

lemma exists_reduce_to_rat : ∀ (D c : ℕ) (T : Finset ℂ), (∀ t ∈ T, IsAlgebraic ℚ t) →
    (∀ t ∈ T, degQ t ≤ D) → (T.filter (fun t => degQ t = D)).card ≤ c →
    ∃ f : ℚ[X], 0 < f.natDegree ∧ (∀ t ∈ T, degQ (aeval t f) = 1) ∧
      (∀ v ∈ critVal f, degQ v = 1) := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ihD =>
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ihc =>
      intro T halg hdeg hcard
      by_cases hD : D ≤ 1
      · refine ⟨X, by simp, ?_, ?_⟩
        · intro t ht
          have h1 := degQ_pos (halg t ht)
          have h2 := hdeg t ht
          rw [aeval_X]
          omega
        · intro v hv
          rw [critVal_X] at hv
          exact absurd hv (Set.notMem_empty v)
      push_neg at hD
      rcases Nat.eq_zero_or_pos (T.filter (fun t => degQ t = D)).card with h0 | hpos
      · refine ihD (D - 1) (by omega) T.card T halg ?_ (Finset.card_filter_le _ _)
        intro t ht
        have hnm : t ∉ T.filter (fun t => degQ t = D) := by
          rw [Finset.card_eq_zero] at h0
          simp [h0]
        simp only [Finset.mem_filter, not_and] at hnm
        have h5 := hnm ht
        have h6 := hdeg t ht
        omega
      obtain ⟨α, hαmem⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at hαmem
      obtain ⟨hαT, hαD⟩ := hαmem
      have hαalg : IsAlgebraic ℚ α := halg α hαT
      set m := minpoly ℚ α with hm
      have hmdeg : m.natDegree = D := hαD
      have hmder : derivative m ≠ 0 := by
        intro hcon
        have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hcon
        omega
      have hmzero : aeval α m = 0 := minpoly.aeval ℚ α
      set T' := T.image (fun t => aeval t m) ∪ critValFinset m with hT'
      have hcritmem : ∀ u ∈ critValFinset m, IsAlgebraic ℚ u ∧ degQ u ≤ D - 1 := by
        intro u hu
        have hu' : u ∈ critVal m := by
          rw [critVal_eq_coe_critValFinset m hmder]; exact_mod_cast hu
        obtain ⟨w, hw, rfl⟩ := hu'
        obtain ⟨hwalg, hwdeg⟩ := degQ_root_derivative_minpoly (α := α) (by omega) hw
        exact ⟨isAlgebraic_aeval hwalg m, le_trans (degQ_aeval_le hwalg m) (by omega)⟩
      have halg' : ∀ u ∈ T', IsAlgebraic ℚ u := by
        intro u hu
        rcases Finset.mem_union.mp hu with h | h
        · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
          exact isAlgebraic_aeval (halg t ht) m
        · exact (hcritmem u h).1
      have hdeg' : ∀ u ∈ T', degQ u ≤ D := by
        intro u hu
        rcases Finset.mem_union.mp hu with h | h
        · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
          exact le_trans (degQ_aeval_le (halg t ht) m) (hdeg t ht)
        · have := (hcritmem u h).2; omega
      have hsub : T'.filter (fun u => degQ u = D) ⊆
          ((T.filter (fun t => degQ t = D)).erase α).image (fun t => aeval t m) := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨huT', huD⟩ := hu
        rcases Finset.mem_union.mp huT' with h | h
        · obtain ⟨t, ht, htu⟩ := Finset.mem_image.mp h
          have hdt : degQ t = D := by
            have h1 : degQ u ≤ degQ t := htu ▸ degQ_aeval_le (halg t ht) m
            have h2 := hdeg t ht
            omega
          have htα : t ≠ α := by
            intro hcon
            rw [hcon, hmzero] at htu
            rw [← htu, degQ_zero] at huD
            omega
          exact Finset.mem_image.mpr
            ⟨t, Finset.mem_erase.mpr ⟨htα, Finset.mem_filter.mpr ⟨ht, hdt⟩⟩, htu⟩
        · exfalso
          have := (hcritmem u h).2
          omega
      have hcard' : (T'.filter (fun u => degQ u = D)).card ≤ c - 1 := by
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_image_le (s := (T.filter (fun t => degQ t = D)).erase α)
          (f := fun t => aeval t m)
        have h3 : ((T.filter (fun t => degQ t = D)).erase α).card =
            (T.filter (fun t => degQ t = D)).card - 1 :=
          Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hαT, hαD⟩)
        omega
      obtain ⟨g, hgdeg, hgeval, hgcrit⟩ := ihc (c - 1) (by omega) T' halg' hdeg' hcard'
      refine ⟨g.comp m, ?_, ?_, ?_⟩
      · rw [natDegree_comp]
        exact Nat.mul_pos hgdeg (by omega)
      · intro t ht
        rw [aeval_comp]
        exact hgeval _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩))
      · intro v hv
        rcases critVal_comp g m hv with ⟨u, hu, huv⟩ | hv'
        · rw [← huv]
          refine hgeval _ (Finset.mem_union_right _ ?_)
          rw [critVal_eq_coe_critValFinset m hmder] at hu
          exact_mod_cast hu
        · exact hgcrit v hv'

/-- The Belyi polynomials really are Belyi maps; in particular `Math2.IsBelyi` is satisfiable. -/
