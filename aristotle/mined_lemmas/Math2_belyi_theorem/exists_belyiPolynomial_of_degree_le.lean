import RequestProject.BelyiPoly

/-!
# Belyi polynomials for finite sets of rational points

A polynomial `f ∈ ℚ[X]` is *Belyi* if it is non-constant and all of its finite critical values
(computed over `ℂ`) lie in `{0, 1}`; viewed as a map `ℙ¹ → ℙ¹` such an `f` is ramified only
above `{0, 1, ∞}`.

The main result of this file is `Math2.exists_belyiPolynomial_of_rat`: for every finite set of
rational numbers there is a Belyi polynomial taking each of them to `0` or `1`.
-/

set_option maxRecDepth 8000

namespace Math2

open Polynomial

/-- `f` is a Belyi polynomial: non-constant, with all finite critical values in `{0, 1}`. -/

lemma exists_belyiPolynomial_of_degree_le (d : ℕ) : ∀ S : Finset ℂ, (∀ s ∈ S, IsIntegral ℚ s) →
    (∀ s ∈ S, algDeg s ≤ d) →
    ∃ f : ℚ[X], IsBelyiPolynomial f ∧ ∀ s ∈ S, aeval s f = 0 ∨ aeval s f = 1 := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    by_cases hd : d ≤ 1
    · -- all marked points are rational
      intro S hint hdeg
      obtain ⟨f, hf, hval⟩ := exists_belyiPolynomial_of_rat (S.image ratPart)
      refine ⟨f, hf, ?_⟩
      intro s hs
      have hq : ∃ q : ℚ, s = (q : ℂ) :=
        exists_rat_of_algDeg_le_one (hint s hs) (le_trans (hdeg s hs) hd)
      have hspec := ratPart_spec hq
      have := hval (ratPart s) (Finset.mem_image.2 ⟨s, hs, rfl⟩)
      rw [← hspec]
      exact aeval_rat_mem this
    · push_neg at hd
      have inner : ∀ k : ℕ, ∀ S : Finset ℂ, (∀ s ∈ S, IsIntegral ℚ s) → (∀ s ∈ S, algDeg s ≤ d) →
          (S.filter (fun s => algDeg s = d)).card ≤ k →
          ∃ f : ℚ[X], IsBelyiPolynomial f ∧ ∀ s ∈ S, aeval s f = 0 ∨ aeval s f = 1 := by
        intro k
        induction k with
        | zero =>
          intro S hint hdeg hcard
          have hempty : S.filter (fun s => algDeg s = d) = ∅ := Finset.card_eq_zero.1 (by omega)
          refine IH (d - 1) (by omega) S hint ?_
          intro s hs
          have hne : algDeg s ≠ d := by
            intro hcon
            have : s ∈ S.filter (fun s => algDeg s = d) := Finset.mem_filter.2 ⟨hs, hcon⟩
            rw [hempty] at this
            simp at this
          have := hdeg s hs
          omega
        | succ k ihk =>
          intro S hint hdeg hcard
          by_cases hne : (S.filter (fun s => algDeg s = d)).Nonempty
          · obtain ⟨alpha, halpha⟩ := hne
            rw [Finset.mem_filter] at halpha
            obtain ⟨halphaS, halphadeg⟩ := halpha
            have hai : IsIntegral ℚ alpha := hint alpha halphaS
            set P : ℚ[X] := minpoly ℚ alpha with hP
            have hPdeg : P.natDegree = d := halphadeg
            have hPne : P ≠ 0 := minpoly.ne_zero hai
            have hPderiv : (derivative P).natDegree < d := by
              rw [← hPdeg]
              exact natDegree_derivative_lt (by rw [hPdeg]; omega)
            have hderivne : derivative P ≠ 0 := by
              intro hcon
              have := natDegree_eq_zero_of_derivative_eq_zero hcon
              rw [hPdeg] at this
              omega
            -- the critical values of `P`
            set crit : Finset ℂ := ((derivative P).aroots ℂ).toFinset.image (fun z => aeval z P)
              with hcrit
            set S' : Finset ℂ := S.image (fun s => aeval s P) ∪ crit with hS'
            have hcritdeg : ∀ t ∈ crit, IsIntegral ℚ t ∧ algDeg t ≤ d - 1 := by
              intro t ht
              rw [hcrit, Finset.mem_image] at ht
              obtain ⟨z, hz, rfl⟩ := ht
              rw [Multiset.mem_toFinset, Polynomial.mem_aroots] at hz
              obtain ⟨-, hz0⟩ := hz
              have hzalg : IsAlgebraic ℚ z := ⟨derivative P, hderivne, hz0⟩
              have hzint : IsIntegral ℚ z := hzalg.isIntegral
              have hdvd : minpoly ℚ z ∣ derivative P := minpoly.dvd ℚ z hz0
              have hzdeg : algDeg z ≤ d - 1 := by
                have h6 : algDeg z ≤ (derivative P).natDegree :=
                  Polynomial.natDegree_le_of_dvd hdvd hderivne
                omega
              exact ⟨isIntegral_aeval hzint P, le_trans (algDeg_aeval_le hzint P) hzdeg⟩
            have hS'int : ∀ t ∈ S', IsIntegral ℚ t := by
              intro t ht
              rw [hS', Finset.mem_union] at ht
              rcases ht with ht | ht
              · rw [Finset.mem_image] at ht
                obtain ⟨s, hs, rfl⟩ := ht
                exact isIntegral_aeval (hint s hs) P
              · exact (hcritdeg t ht).1
            have hS'deg : ∀ t ∈ S', algDeg t ≤ d := by
              intro t ht
              rw [hS', Finset.mem_union] at ht
              rcases ht with ht | ht
              · rw [Finset.mem_image] at ht
                obtain ⟨s, hs, rfl⟩ := ht
                exact le_trans (algDeg_aeval_le (hint s hs) P) (hdeg s hs)
              · exact le_trans (hcritdeg t ht).2 (by omega)
            -- the number of points of maximal degree strictly decreases
            have hsub : S'.filter (fun t => algDeg t = d) ⊆
                ((S.filter (fun s => algDeg s = d)).erase alpha).image (fun s => aeval s P) := by
              intro t ht
              rw [Finset.mem_filter] at ht
              obtain ⟨htS', htdeg⟩ := ht
              rw [hS', Finset.mem_union] at htS'
              rcases htS' with htS' | htS'
              · rw [Finset.mem_image] at htS'
                obtain ⟨s, hs, rfl⟩ := htS'
                have hsdeg : algDeg s = d :=
                  le_antisymm (hdeg s hs) (by rw [← htdeg]; exact algDeg_aeval_le (hint s hs) P)
                have hsalpha : s ≠ alpha := by
                  rintro rfl
                  have h0 : aeval s P = 0 := by rw [hP]; exact minpoly.aeval ℚ s
                  rw [h0] at htdeg
                  have : algDeg (0 : ℂ) = 1 := by
                    rw [algDeg, minpoly.zero, natDegree_X]
                  omega
                exact Finset.mem_image.2 ⟨s, Finset.mem_erase.2 ⟨hsalpha,
                  Finset.mem_filter.2 ⟨hs, hsdeg⟩⟩, rfl⟩
              · exfalso
                have := (hcritdeg t htS').2
                omega
            have hcard' : (S'.filter (fun t => algDeg t = d)).card ≤ k := by
              have h2 := Finset.card_le_card hsub
              have h3 := Finset.card_image_le
                (s := (S.filter (fun s => algDeg s = d)).erase alpha) (f := fun s => aeval s P)
              have h4 : ((S.filter (fun s => algDeg s = d)).erase alpha).card
                  = (S.filter (fun s => algDeg s = d)).card - 1 :=
                Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨halphaS, halphadeg⟩)
              have h5 : 1 ≤ (S.filter (fun s => algDeg s = d)).card :=
                Finset.card_pos.2 ⟨alpha, Finset.mem_filter.2 ⟨halphaS, halphadeg⟩⟩
              omega
            obtain ⟨g, hgB, hgval⟩ := ihk S' hS'int hS'deg hcard'
            refine ⟨g.comp P, ?_, ?_⟩
            · refine IsBelyiPolynomial.comp (by rw [hPdeg]; omega) hgB ?_
              intro z hz
              have hmem : aeval z P ∈ S' := by
                rw [hS', Finset.mem_union]
                right
                rw [hcrit]
                exact Finset.mem_image.2 ⟨z, by
                  rw [Multiset.mem_toFinset, Polynomial.mem_aroots]
                  exact ⟨hderivne, hz⟩, rfl⟩
              exact hgval _ hmem
            · intro s hs
              rw [aeval_comp]
              exact hgval _ (by
                rw [hS', Finset.mem_union]
                exact Or.inl (Finset.mem_image.2 ⟨s, hs, rfl⟩))
          · rw [Finset.not_nonempty_iff_eq_empty] at hne
            refine IH (d - 1) (by omega) S hint ?_
            intro s hs
            have hne' : algDeg s ≠ d := by
              intro hcon
              have : s ∈ S.filter (fun s => algDeg s = d) := Finset.mem_filter.2 ⟨hs, hcon⟩
              rw [hne] at this
              simp at this
            have := hdeg s hs
            omega
      intro S hint hdeg
      exact inner _ S hint hdeg le_rfl

/-- **Belyi's theorem** for the projective line with marked points.

For a finite set `S ⊆ ℂ` of marked points on `ℙ¹`, the following are equivalent:

* every marked point is algebraic over `ℚ`, i.e. the marked curve `(ℙ¹, S)` is defined over `ℚ̄`;
* there is a Belyi map for it, namely a non-constant `f ∈ ℚ[X]` — a morphism `ℙ¹ → ℙ¹` defined
  over `ℚ` which is ramified only above `{0, 1, ∞}`, since all its finite critical values lie in
  `{0, 1}` and `∞` is totally ramified — carrying every marked point into `{0, 1}`, i.e. into
  the fibre above `{0, 1, ∞}`. -/
