/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian

/-! # Admissible gap ranges and the Hardy–Littlewood singular series for prime pairs

For a gap `g` we consider the two–element pattern `{0, g}`.  Such a pattern is
*admissible* when, for every prime `p`, its residues do not cover all of `ZMod p`.
The Hardy–Littlewood singular series of the pattern `{0, g}` is
`𝔖(g) = 2 C₂ ∏_{p ∣ g, p odd} (p-1)/(p-2)` for even `g`, and `0` for odd `g`;
here we work with the arithmetic factor `∏_{p ∣ g, p odd} (p-1)/(p-2)` and with the
convention that the factor vanishes for odd `g` (matching the vanishing of `𝔖`).
-/

/-- A finite pattern `H ⊆ ℤ` is *admissible* if for every prime `p` some residue class
mod `p` is missed by `H`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- The two–element pattern determined by a gap `g`. -/
def gapSet (g : ℕ) : Finset ℤ := {0, (g : ℤ)}

/-- The arithmetic factor `∏_{p ∣ g, p odd} (p-1)/(p-2)` of the Hardy–Littlewood
singular series of the pair `{0, g}`, extended by `0` on odd gaps (where the singular
series itself vanishes). -/
noncomputable def singularSeriesFactor (g : ℕ) : ℝ :=
  if Even g then ∏ p ∈ g.primeFactors with p ≠ 2, ((p : ℝ) - 1) / ((p : ℝ) - 2) else 0

/-- A pattern with fewer elements than `p` misses a residue class mod `p`. -/
lemma exists_missing_residue (p : ℕ) (hp : p.Prime) (H : Finset ℤ) (hcard : H.card < p) :
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  set S : Finset (ZMod p) := H.image (fun x : ℤ => (x : ZMod p)) with hS
  have h1 : S.card < Fintype.card (ZMod p) := by
    have h := Finset.card_image_le (s := H) (f := fun x : ℤ => (x : ZMod p))
    rw [← hS] at h
    rw [ZMod.card]
    omega
  have h2 : S ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ] at h1
    omega
  obtain ⟨r, hr⟩ : ∃ r : ZMod p, r ∉ S := by
    by_contra hcon
    push_neg at hcon
    exact h2 (Finset.eq_univ_iff_forall.mpr hcon)
  refine ⟨r, fun h hh hcontra => hr ?_⟩
  rw [hS, ← hcontra]
  exact Finset.mem_image_of_mem _ hh

/-- Even gaps give admissible pairs. -/
lemma admissible_gapSet_of_even {g : ℕ} (hg : Even g) : Admissible (gapSet g) := by
  intro p hp
  rcases eq_or_ne p 2 with rfl | hp2
  · refine ⟨1, ?_⟩
    intro h hh
    have hg0 : ((g : ℤ) : ZMod 2) = 0 := by
      push_cast
      exact ZMod.natCast_eq_zero_iff_even.mpr hg
    simp only [gapSet, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · simp only [Int.cast_zero]
      decide
    · rw [hg0]
      decide
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    refine exists_missing_residue p hp _ ?_
    have : (gapSet g).card ≤ 2 := by
      simpa [gapSet] using Finset.card_insert_le (0 : ℤ) {(g : ℤ)}
    omega

/-- Odd gaps give inadmissible pairs (the residues cover `ZMod 2`). -/
lemma not_admissible_gapSet_of_odd {g : ℕ} (hg : ¬ Even g) : ¬ Admissible (gapSet g) := by
  intro hA
  obtain ⟨r, hr⟩ := hA 2 Nat.prime_two
  have hg1 : ((g : ℤ) : ZMod 2) = 1 := by
    rw [Nat.not_even_iff_odd] at hg
    obtain ⟨k, hk⟩ := hg
    subst hk
    push_cast
    ring_nf
    simp [show ((2 : ZMod 2)) = 0 by decide]
  have h0 : ((0 : ℤ) : ZMod 2) ≠ r := hr 0 (by simp [gapSet])
  have h1 : ((g : ℤ) : ZMod 2) ≠ r := hr _ (by simp [gapSet])
  rw [hg1] at h1
  simp only [Int.cast_zero] at h0
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) r with rfl | rfl
  · exact h0 rfl
  · exact h1 rfl

/-- On even gaps every local factor is at least one. -/
lemma one_le_singularSeriesFactor {g : ℕ} (hg : Even g) : 1 ≤ singularSeriesFactor g := by
  rw [singularSeriesFactor, if_pos hg]
  have key : ∀ p ∈ g.primeFactors.filter (fun p => p ≠ 2),
      (1 : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := ?_
  · simpa using Finset.prod_le_prod (f := fun _ : ℕ => (1 : ℝ))
      (g := fun p : ℕ => ((p : ℝ) - 1) / ((p : ℝ) - 2)) (fun i _ => zero_le_one) key
  intro p hp
  simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
  obtain ⟨⟨hpp, _, _⟩, hp2⟩ := hp
  have hp3 : 3 ≤ p := by
    have := hpp.two_le
    omega
  have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The singular series factor is positive exactly on the even gaps. -/
lemma singularSeriesFactor_pos_iff (g : ℕ) : 0 < singularSeriesFactor g ↔ Even g := by
  constructor
  · intro h
    by_contra hg
    rw [singularSeriesFactor, if_neg hg] at h
    exact lt_irrefl 0 h
  · intro hg
    have := one_le_singularSeriesFactor hg
    linarith

/-- Explicit values of the singular series factor at the even gaps in `[1350, 1360]`. -/
theorem SingularSeriesGapsValues13501360 :
    singularSeriesFactor 1350 = 8 / 3 ∧
    singularSeriesFactor 1352 = 12 / 11 ∧
    singularSeriesFactor 1354 = 676 / 675 ∧
    singularSeriesFactor 1356 = 224 / 111 ∧
    singularSeriesFactor 1358 = 576 / 475 ∧
    singularSeriesFactor 1360 = 64 / 45 := by
  have h1350 : Nat.primeFactors 1350 = {2, 3, 5} := by decide +kernel
  have h1352 : Nat.primeFactors 1352 = {2, 13} := by decide +kernel
  have h1354 : Nat.primeFactors 1354 = {2, 677} := by decide +kernel
  have h1356 : Nat.primeFactors 1356 = {2, 3, 113} := by decide +kernel
  have h1358 : Nat.primeFactors 1358 = {2, 7, 97} := by decide +kernel
  have h1360 : Nat.primeFactors 1360 = {2, 5, 17} := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [singularSeriesFactor, if_pos (by decide : Even 1350),
      if_pos (by decide : Even 1352), if_pos (by decide : Even 1354),
      if_pos (by decide : Even 1356), if_pos (by decide : Even 1358),
      if_pos (by decide : Even 1360), h1350, h1352, h1354, h1356, h1358, h1360] <;>
    norm_num [Finset.filter_insert, Finset.filter_singleton, Finset.prod_insert]

/-- **Admissible gap ranges, `1350 ≤ g ≤ 1360`.**  For every gap `g` in this range:
the pair pattern `{0, g}` is admissible exactly when `g` is even, which happens exactly
when the Hardy–Littlewood singular series factor of the pattern is positive; moreover on
this range that factor lies in `[1, 8/3]` for the even gaps, the extreme value `8/3`
being attained at `g = 1350`. -/
theorem SingularSeriesGaps13501360 (g : ℕ) (hg : g ∈ Finset.Icc 1350 1360) :
    (Admissible (gapSet g) ↔ Even g) ∧
    (0 < singularSeriesFactor g ↔ Even g) ∧
    (Even g → 1 ≤ singularSeriesFactor g) ∧
    singularSeriesFactor g ≤ 8 / 3 := by
  obtain ⟨v1350, v1352, v1354, v1356, v1358, v1360⟩ := SingularSeriesGapsValues13501360
  refine ⟨⟨?_, admissible_gapSet_of_even⟩, singularSeriesFactor_pos_iff g,
    fun h => one_le_singularSeriesFactor h, ?_⟩
  · intro hA
    by_contra hodd
    exact not_admissible_gapSet_of_odd hodd hA
  · simp only [Finset.mem_Icc] at hg
    obtain ⟨hg1, hg2⟩ := hg
    interval_cases g <;>
      first
        | (rw [singularSeriesFactor, if_neg (by decide)]; norm_num)
        | (rw [v1350])
        | (rw [v1352]; norm_num)
        | (rw [v1354]; norm_num)
        | (rw [v1356]; norm_num)
        | (rw [v1358]; norm_num)
        | (rw [v1360]; norm_num)

end Brockian

