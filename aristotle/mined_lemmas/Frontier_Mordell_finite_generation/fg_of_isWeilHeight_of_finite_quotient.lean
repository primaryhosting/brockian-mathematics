/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The doubling endomorphism `P ↦ 2 • P` of an additive commutative group. -/

theorem fg_of_isWeilHeight_of_finite_quotient (h : A → ℝ) (hh : IsWeilHeight A h)
    (hq : Finite (A ⧸ (doubleHom A).range)) : AddGroup.FG A := by
  classical
  set K := (doubleHom A).range with hK
  set rep : (A ⧸ K) → A := fun c => Quotient.out c with hrepdef
  have htr : ∀ c : A ⧸ K, ∃ C : ℝ, ∀ P : A, h (P + (-(rep c))) ≤ 2 * h P + C :=
    fun c => hh.translate _
  choose Cf hCf using htr
  obtain ⟨C, hC⟩ := Finite.exists_le Cf
  obtain ⟨D, hD⟩ := hh.double
  set B : ℝ := (C + D) / 2 with hB
  set S : Set A := Set.range rep ∪ {P | h P ≤ B} with hS
  have hSfin : S.Finite := (Set.finite_range rep).union (hh.finite_le B)
  set G := AddSubgroup.closure S with hG
  have hsub : ∀ x ∈ S, x ∈ G := fun x hx => AddSubgroup.subset_closure hx
  -- The key descent step: any point outside `G` admits a point outside `G` of smaller height.
  have key : ∀ P : A, P ∉ G → ∃ P' : A, P' ∉ G ∧ h P' < h P := by
    intro P hP
    have hPB : B < h P := by
      by_contra hle
      push_neg at hle
      exact hP (hsub P (Or.inr hle))
    set c : A ⧸ K := QuotientAddGroup.mk P with hc
    have hrepc : (QuotientAddGroup.mk (rep c) : A ⧸ K) = c := QuotientAddGroup.out_eq' c
    have hmem : P - rep c ∈ K := by
      rw [← QuotientAddGroup.eq_zero_iff]
      rw [QuotientAddGroup.mk_sub, hrepc, hc]
      simp
    obtain ⟨P', hP'⟩ := hmem
    have hPeq : P = (2 : ℕ) • P' + rep c := by
      have : (2 : ℕ) • P' = P - rep c := hP'
      rw [this]; abel
    have h1 : h ((2 : ℕ) • P') ≤ 2 * h P + C := by
      have : (2 : ℕ) • P' = P + (-(rep c)) := by
        rw [show ((2 : ℕ) • P' : A) = P - rep c from hP']; abel
      calc h ((2 : ℕ) • P') = h (P + (-(rep c))) := by rw [this]
        _ ≤ 2 * h P + Cf c := hCf c P
        _ ≤ 2 * h P + C := by linarith [hC c]
    have h2 : 4 * h P' ≤ h ((2 : ℕ) • P') + D := hD P'
    have h3 : h P' < h P := by
      have : B < h P := hPB
      rw [hB] at this
      linarith
    refine ⟨P', ?_, h3⟩
    intro hP'G
    apply hP
    have hrepG : rep c ∈ G := hsub _ (Or.inl ⟨c, rfl⟩)
    rw [hPeq]
    exact AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hP'G 2) hrepG
  -- Minimal counterexample argument.
  have htop : G = ⊤ := by
    by_contra hne
    obtain ⟨P, hP⟩ : ∃ P : A, P ∉ G := by
      by_contra hall
      push_neg at hall
      exact hne (eq_top_iff.mpr fun x _ => hall x)
    have hXfin : {R : A | R ∉ G ∧ h R ≤ h P}.Finite :=
      (hh.finite_le (h P)).subset (fun x hx => hx.2)
    have hXne : hXfin.toFinset.Nonempty := ⟨P, by simp [hXfin.mem_toFinset, hP]⟩
    obtain ⟨R, hRmem, hmin⟩ := hXfin.toFinset.exists_min_image h hXne
    rw [hXfin.mem_toFinset] at hRmem
    obtain ⟨R', hR'G, hR'lt⟩ := key R hRmem.1
    have : R' ∈ hXfin.toFinset := by
      rw [hXfin.mem_toFinset]
      exact ⟨hR'G, le_of_lt (lt_of_lt_of_le hR'lt hRmem.2)⟩
    exact absurd (hmin R' this) (not_le.mpr hR'lt)
  exact AddGroup.fg_iff.mpr ⟨S, htop, hSfin⟩

/-- Sanity check that the hypotheses of the descent theorem are satisfiable and not vacuous:
on a finite abelian group the zero function is a Weil height and the quotient by `2A` is
finite, so the descent theorem indeed yields finite generation. -/
