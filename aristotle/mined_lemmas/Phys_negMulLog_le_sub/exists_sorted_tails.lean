import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` to be the very first command of a module, so the
requested header block appears immediately after the single `import Mathlib` line.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace Phys

/-! ## Elementary entropy inequalities -/

/-- Gibbs-type pointwise bound: for `x ≥ 0` and a reference weight `r > 0`,
`-x log x ≤ (r - x) - x log r`. -/

theorem exists_sorted_tails (lam : A → ℝ) (hnn : ∀ i, 0 ≤ lam i) (hs1 : ∑ i, lam i = 1)
    (f : ℕ → ℝ)
    (hdecay : ∀ k : ℕ, ∃ s : Finset A, s.card ≤ k ∧ ∑ i ∈ sᶜ, lam i ≤ f k) :
    ∃ e : Fin (Fintype.card A) ≃ A, ∀ k : ℕ,
      ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card A) => k ≤ (i : ℕ)), lam (e i) ≤ f k := by
  classical
  set N := Fintype.card A with hN
  obtain ⟨e, hanti⟩ : ∃ e : Fin N ≃ A, Antitone (fun i => lam (e i)) := by
    let g : Fin N ≃ A := (Fintype.equivFin A).symm
    let f0 : Fin N → ℝ := fun i => -lam (g i)
    refine ⟨(Tuple.sort f0).trans g, ?_⟩
    have hm : Monotone (f0 ∘ (Tuple.sort f0)) := Tuple.monotone_sort f0
    intro a b hab
    have h := hm hab
    simp only [Function.comp_apply, f0, neg_le_neg_iff] at h
    simpa [Equiv.trans] using h
  refine ⟨e, ?_⟩
  set p : Fin N → ℝ := fun i => lam (e i) with hp
  have hpnn : ∀ i, 0 ≤ p i := fun i => hnn _
  have hpsum : ∑ i, p i = 1 := by rw [← hs1]; exact Equiv.sum_comp e lam
  intro k
  obtain ⟨s, hs, hsum⟩ := hdecay k
  set t : Finset (Fin N) := s.map e.symm.toEmbedding with ht
  have hcard : t.card ≤ k := by simpa [ht] using hs
  have hts : ∑ i ∈ t, p i = ∑ a ∈ s, lam a := by
    rw [ht, Finset.sum_map]
    exact Finset.sum_congr rfl (fun a _ => by simp [hp])
  have hsplit : ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i
      = 1 - ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), p i := by
    have h := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin N))
      (fun i : Fin N => (i : ℕ) < k) p
    rw [hpsum] at h
    have hcongr : (Finset.univ.filter (fun i : Fin N => ¬ ((i : ℕ) < k)))
        = Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)) := by
      ext i; simp
    rw [hcongr] at h
    linarith
  have hdom := sum_le_sum_first hanti hpnn t k hcard
  have hcompl : ∑ i ∈ sᶜ, lam i = 1 - ∑ a ∈ s, lam a := by
    have h := Finset.sum_add_sum_compl s lam
    rw [hs1] at h
    linarith
  rw [hsplit]
  rw [hts] at hdom
  rw [hcompl] at hsum
  linarith

