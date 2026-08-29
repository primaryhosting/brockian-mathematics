/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian

open DihedralGroup

noncomputable section

/-! ## The root of unity -/

/-- A primitive `n`-th root of unity in `ℂ`. -/

theorem isoPlane_irreducible (n : ℕ) [NeZero n] (k : ZMod n)
    (W : Submodule ℂ (ZMod n → ℂ)) (hW : W ≤ isoPlane n k)
    (hinv : ∀ g : DihedralGroup n, Submodule.map (ngonRep n g) W ≤ W) :
    W = ⊥ ∨ W = isoPlane n k := by
  rcases eq_or_ne W ⊥ with h | h
  · exact Or.inl h
  refine Or.inr (le_antisymm hW ?_)
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).1 h
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 (hW hwW)
  -- it suffices to show that `evec n k ∈ W`
  have key : evec n k ∈ W → isoPlane n k ≤ W := by
    intro hk
    have hk' : evec n (-k) ∈ W := by
      have := hinv (sr 0) ⟨evec n k, hk, rfl⟩
      rwa [ngonRep_sr_evec, evec_zero_arg, one_smul] at this
    rw [isoPlane, Submodule.span_le]
    rintro v (rfl | rfl)
    · exact hk
    · exact hk'
  rcases eq_or_ne k (-k) with hkk | hkk
  · -- degenerate case: the plane is a line
    apply key
    have hkk' : evec n (-k) = evec n k := by rw [← hkk]
    have hw : ((a + b) • evec n k : ZMod n → ℂ) = w := by
      rw [add_smul, ← hab, hkk']
    have hab0 : a + b ≠ 0 := by
      intro h0
      apply hw0
      rw [← hw, h0, zero_smul]
    have : (a + b)⁻¹ • w ∈ W := Submodule.smul_mem _ _ hwW
    rwa [← hw, smul_smul, inv_mul_cancel₀ hab0, one_smul] at this
  · -- generic case: separate the two rotation eigenlines
    obtain ⟨i, hi⟩ := exists_evec_ne n k hkk
    have hrot : (evec n k i) • (a • evec n k) + (evec n (-k) i) • (b • evec n (-k)) ∈ W := by
      have hmem := hinv (r i) ⟨w, hwW, rfl⟩
      have : (ngonRep n (r i)) w
          = (evec n k i) • (a • evec n k) + (evec n (-k) i) • (b • evec n (-k)) := by
        rw [← hab, map_add, LinearMap.map_smul, LinearMap.map_smul, ngonRep_r_evec,
          ngonRep_r_evec, smul_comm, smul_comm (b : ℂ)]
      rwa [this] at hmem
    -- subtract `evec n (-k) i • w` to isolate the `evec n k` component
    have h1 : ((evec n k i - evec n (-k) i) * a) • evec n k ∈ W := by
      have hsub : ((evec n k i - evec n (-k) i) * a) • evec n k
          = ((evec n k i) • (a • evec n k) + (evec n (-k) i) • (b • evec n (-k)))
            - (evec n (-k) i) • w := by
        rw [← hab]
        simp only [smul_add, smul_smul]
        rw [sub_mul]
        module
      rw [hsub]
      exact Submodule.sub_mem _ hrot (Submodule.smul_mem _ _ hwW)
    have h2 : ((evec n (-k) i - evec n k i) * b) • evec n (-k) ∈ W := by
      have hsub : ((evec n (-k) i - evec n k i) * b) • evec n (-k)
          = ((evec n k i) • (a • evec n k) + (evec n (-k) i) • (b • evec n (-k)))
            - (evec n k i) • w := by
        rw [← hab]
        simp only [smul_add, smul_smul]
        rw [sub_mul]
        module
      rw [hsub]
      exact Submodule.sub_mem _ hrot (Submodule.smul_mem _ _ hwW)
    have hd : evec n k i - evec n (-k) i ≠ 0 := sub_ne_zero.2 hi
    have hd' : evec n (-k) i - evec n k i ≠ 0 := sub_ne_zero.2 (Ne.symm hi)
    rcases eq_or_ne a 0 with rfl | ha
    · -- then `b ≠ 0`, so `evec n (-k) ∈ W`, hence `evec n k ∈ W`
      have hb : b ≠ 0 := by
        intro rfl
        exact hw0 (by rw [← hab]; simp)
      have hmem : evec n (-k) ∈ W := by
        have hc : ((evec n (-k) i - evec n k i) * b) ≠ 0 := mul_ne_zero hd' hb
        have := Submodule.smul_mem W (((evec n (-k) i - evec n k i) * b)⁻¹) h2
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
      apply key
      have := hinv (sr 0) ⟨evec n (-k), hmem, rfl⟩
      rwa [ngonRep_sr_evec, evec_zero_arg, one_smul, neg_neg] at this
    · apply key
      have hc : ((evec n k i - evec n (-k) i) * a) ≠ 0 := mul_ne_zero hd ha
      have := Submodule.smul_mem W (((evec n k i - evec n (-k) i) * a)⁻¹) h1
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-! ## The fusion rule: pentagon ⊗ pentagon -/

/-- The pointwise product of vectors from the `j`-th and `k`-th isotypic planes lies in
the sum of the `(j+k)`-th and `(j-k)`-th isotypic planes. -/
