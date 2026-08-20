import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial
open scoped IntermediateField

namespace Math2

/-- A *Belyi map* (in the genus-zero, polynomial model): a nonconstant polynomial with
rational coefficients, viewed as a morphism `ℙ¹ → ℙ¹` defined over `ℚ`, all of whose
finite critical values lie in `{0, 1}`.  Being a polynomial, such a map is totally
ramified over `∞`, so it is ramified only above `{0, 1, ∞}`. -/

theorem belyi_descent_step (d : ℕ)
    (ih : ∀ S : Finset ℂ, (∀ s ∈ S, IsAlgebraic ℚ s) → (∀ s ∈ S, adeg s ≤ d) →
      BelyiFor (S : Set ℂ)) (hd : 1 ≤ d) :
    ∀ (k : ℕ) (S : Finset ℂ), (∀ s ∈ S, IsAlgebraic ℚ s) → (∀ s ∈ S, adeg s ≤ d + 1) →
      (S.filter (fun s => adeg s = d + 1)).card ≤ k → BelyiFor (S : Set ℂ) := by
  classical
  intro k
  induction k with
  | zero =>
    intro S halg hdeg hcard
    refine ih S halg fun s hs => ?_
    have hnot : s ∉ S.filter (fun s => adeg s = d + 1) := by
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)]; simp
    simp only [Finset.mem_filter, not_and] at hnot
    have h1 := hnot hs
    have h2 := hdeg s hs
    omega
  | succ k ihk =>
    intro S halg hdeg hcard
    by_cases hall : ∀ s ∈ S, adeg s ≤ d
    · exact ih S halg hall
    · push_neg at hall
      obtain ⟨α, hαS, hα⟩ := hall
      have hαdeg : adeg α = d + 1 := le_antisymm (hdeg α hαS) hα
      have hαalg : IsAlgebraic ℚ α := halg α hαS
      have hαint : IsIntegral ℚ α := hαalg.isIntegral
      set m : ℚ[X] := minpoly ℚ α with hm
      have hmdeg : m.natDegree = d + 1 := hαdeg
      have hderivdeg : (derivative m).natDegree ≤ d := by
        have := Polynomial.natDegree_derivative_lt (p := m) (by omega)
        omega
      have hderiv0 : derivative m ≠ 0 := by
        intro h0
        have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero (R := ℚ) h0
        omega
      have hmα : aeval α m = 0 := minpoly.aeval ℚ α
      set C₁ : Finset ℂ := ((derivative m).aroots ℂ).toFinset with hC₁
      have hC₁mem : ∀ z : ℂ, aeval z (derivative m) = 0 → z ∈ C₁ := by
        intro z hz
        rw [hC₁, Multiset.mem_toFinset, Polynomial.mem_aroots]
        exact ⟨hderiv0, hz⟩
      have hC₁deg : ∀ z ∈ C₁, IsAlgebraic ℚ z ∧ adeg z ≤ d := by
        intro z hz
        rw [hC₁, Multiset.mem_toFinset, Polynomial.mem_aroots] at hz
        obtain ⟨-, hz2⟩ := hz
        refine ⟨⟨derivative m, hderiv0, hz2⟩, ?_⟩
        have hdle := minpoly.degree_le_of_ne_zero ℚ z hderiv0 hz2
        have h2 : adeg z ≤ (derivative m).natDegree := Polynomial.natDegree_le_natDegree hdle
        omega
      set S' : Finset ℂ := S.image (fun s => aeval s m) ∪ C₁.image (fun z => aeval z m) with hS'
      have hS'alg : ∀ x ∈ S', IsAlgebraic ℚ x := by
        intro x hx
        rw [hS', Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
        rcases hx with ⟨s, hs, rfl⟩ | ⟨z, hz, rfl⟩
        · exact isAlgebraic_aeval (halg s hs) m
        · exact isAlgebraic_aeval (hC₁deg z hz).1 m
      have hS'deg : ∀ x ∈ S', adeg x ≤ d + 1 := by
        intro x hx
        rw [hS', Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
        rcases hx with ⟨s, hs, rfl⟩ | ⟨z, hz, rfl⟩
        · exact le_trans (adeg_aeval_le (halg s hs) m) (hdeg s hs)
        · exact le_trans (le_trans (adeg_aeval_le (hC₁deg z hz).1 m) (hC₁deg z hz).2) (by omega)
      have hzero : adeg (0 : ℂ) = 1 := minpoly.natDegree_eq_one_iff.mpr ⟨0, by simp⟩
      have hαfilter : α ∈ S.filter (fun s => adeg s = d + 1) := Finset.mem_filter.mpr ⟨hαS, hαdeg⟩
      have hcard' : (S'.filter (fun s => adeg s = d + 1)).card ≤ k := by
        have hsub : S'.filter (fun s => adeg s = d + 1) ⊆
            ((S.filter (fun s => adeg s = d + 1)).erase α).image (fun s => aeval s m) := by
          intro x hx
          rw [Finset.mem_filter] at hx
          obtain ⟨hxmem, hxdeg⟩ := hx
          rw [hS', Finset.mem_union, Finset.mem_image, Finset.mem_image] at hxmem
          rcases hxmem with ⟨s, hs, rfl⟩ | ⟨z, hz, rfl⟩
          · refine Finset.mem_image.mpr
              ⟨s, Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hs, ?_⟩⟩, rfl⟩
            · rintro rfl
              rw [hmα] at hxdeg
              omega
            · have h1 := adeg_aeval_le (halg s hs) m
              have h2 := hdeg s hs
              omega
          · exfalso
            have h1 := adeg_aeval_le (hC₁deg z hz).1 m
            have h2 := (hC₁deg z hz).2
            omega
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_image_le (s := (S.filter (fun s => adeg s = d + 1)).erase α)
          (f := fun s => aeval s m)
        have h3 := Finset.card_erase_of_mem hαfilter
        have h4 : 1 ≤ (S.filter (fun s => adeg s = d + 1)).card := Finset.card_pos.mpr ⟨α, hαfilter⟩
        omega
      refine belyi_comp m (by omega) _ _ ?_ ?_ (ihk S' hS'alg hS'deg hcard')
      · intro z hz
        refine Finset.mem_coe.mpr ?_
        rw [hS', Finset.mem_union]
        exact Or.inr (Finset.mem_image_of_mem _ (hC₁mem z hz))
      · intro s hs
        refine Finset.mem_coe.mpr ?_
        rw [hS', Finset.mem_union]
        exact Or.inl (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hs))

/-- Belyi's theorem for finite sets of algebraic numbers of bounded degree, by induction on the
degree bound. -/
