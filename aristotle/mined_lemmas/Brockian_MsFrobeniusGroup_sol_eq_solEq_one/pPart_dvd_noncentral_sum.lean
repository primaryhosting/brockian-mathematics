import Mathlib

/-!
# Frobenius's theorem

For a finite group `G` and any `n`, `gcd (n, |G|)` divides the number of solutions of `xⁿ = 1`.

The proof is organised as follows.

* `sol G n` is the number of solutions of `x ^ n = 1`, `solEq n y` the number of solutions of
  `x ^ n = y`.
* `solEq_prime_pow_dvd`: if `y` has order `p ^ k` with `k ≥ 1`, then `p ^ a` divides the number
  of solutions of `x ^ (p ^ a) = y`.  (Each solution generates a cyclic group of order `p ^ (a+k)`
  containing `y`, and each such cyclic subgroup contains exactly `p ^ a` solutions.)
* Consequently `sol G (p ^ (a+1)) ≡ sol G (p ^ a) [MOD p ^ a]`, so all the numbers
  `sol G (p ^ b)` for `b ≥ a` are congruent mod `p ^ a`.
* `sol_mul_eq_sum`: writing `n = p ^ α * u` with `p ∤ u`, decomposing an element into its
  `p`-part and `p'`-part gives `sol G n = ∑_{w ^ u = 1} sol (centralizer w) (p ^ α)`.
* `pPart_dvd_sol_pPart` (the key theorem): the number of `p`-elements of `G` is divisible by the
  order of a Sylow `p`-subgroup.  This follows by induction on `|G|` from the previous identity
  applied to `n = |G|`, grouping the sum into conjugacy classes.
* Everything is then assembled.
-/

namespace Brockian.MsFrobeniusGroup

open scoped Classical
open Finset

universe u

variable {G : Type u} [Group G]

/-- The number of solutions of `x ^ n = 1` in `G`. -/

lemma pPart_dvd_noncentral_sum [Fintype G] {p : ℕ} (hp : p.Prime)
    (IH : ∀ (H : Type u) [Group H] [Fintype H], Nat.card H < Nat.card G →
      p ^ ((Nat.card H).factorization p) ∣ sol H (p ^ ((Nat.card H).factorization p)))
    (m : ℕ) :
    p ^ ((Nat.card G).factorization p) ∣
      ∑ w ∈ univ.filter (fun w : G => w ^ m = 1 ∧ w ∉ Subgroup.center G),
        sol ↥(Subgroup.centralizer ({w} : Set G)) (p ^ ((Nat.card G).factorization p)) := by
  refine dvd_sum_of_conj_invariant _ ?_ _ ?_ ?_
  · -- Show sol in centralizer is conjugation-invariant
    exact fun g w => sol_centralizer_conj g w _
  · -- Show the set is closed under conjugation
    intro g w hw
    simp at hw ⊢
    refine ⟨hw.1, ?_⟩
    intro hw_cen
    apply hw.2
    rw [Subgroup.mem_center_iff] at hw_cen ⊢
    intro h
    have := hw_cen (g * h * g⁻¹)
    simp at this
    simpa [mul_assoc] using this
  · -- Show d divides index * f w for each w
    intro w hw
    simp at hw
    -- The centralizer of a non-central element is a proper subgroup
    have hne : (Subgroup.centralizer {w} : Set G) ≠ Set.univ := by
      intro h.eq_univ
      apply hw.2
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ (Subgroup.centralizer {w} : Set G) := h.eq_univ ▸ Set.mem_univ g
      simp [Subgroup.mem_centralizer_iff] at this
      exact this.symm
    have hcard : Nat.card ↥(Subgroup.centralizer {w}) < Nat.card G := by
      have hproper : (Subgroup.centralizer {w} : Subgroup G) ≠ ⊤ := by
        intro h.eq_top
        apply hne
        rw [h.eq_top, Subgroup.coe_top]
      have hcard_eq : (Nat.card ↥(Subgroup.centralizer {w})) * (Subgroup.centralizer {w}).index = Nat.card G := by
        exact Subgroup.card_mul_index _
      have hidx_pos : 0 < (Subgroup.centralizer {w}).index := by
        by_contra h
        push Not at h
        simp [Nat.le_zero.mp h] at hcard_eq
        exact Nat.ne_of_lt (Fintype.card_pos) hcard_eq
      have hidx_gt_one : 1 < (Subgroup.centralizer {w}).index := by
        by_contra h_le
        push Not at h_le
        have h_eq : (Subgroup.centralizer {w}).index = 1 := by omega
        exact hproper (Subgroup.index_eq_one.mp h_eq)
      have hcard_pos_C : 0 < Nat.card ↥(Subgroup.centralizer {w}) := Nat.card_pos (α := ↥(Subgroup.centralizer {w}))
      have hcard_lt : Nat.card ↥(Subgroup.centralizer {w}) < Nat.card G := by
        have h := hcard_eq
        calc Nat.card ↥(Subgroup.centralizer {w})
            = Nat.card ↥(Subgroup.centralizer {w}) * 1 := by ring
          _ < Nat.card ↥(Subgroup.centralizer {w}) * (Subgroup.centralizer {w}).index := by nlinarith
          _ = Nat.card G := h
      exact hcard_lt
    -- Apply IH to centralizer
    haveI : Nonempty ↥(Subgroup.centralizer {w}) := ⟨⟨w, by simp [Subgroup.mem_centralizer_iff]⟩⟩
    have hiht := IH ↥(Subgroup.centralizer {w}) hcard
    -- Since centralizer ≤ G, (Nat.card centralizer).factorization p ≤ (Nat.card G).factorization p
    have hv_le : (Nat.card ↥(Subgroup.centralizer {w})).factorization p
                ≤ (Nat.card G).factorization p := by
      have hdvd : Nat.card ↥(Subgroup.centralizer {w}) ∣ Nat.card G := by
        have := Subgroup.card_mul_index (Subgroup.centralizer {w})
        exact ⟨_, this.symm⟩
      obtain ⟨k, hk⟩ := hdvd
      have hk_ne : k ≠ 0 := Nat.ne_of_gt (by nlinarith : 0 < k)
      rw [hk, Nat.factorization_mul (by simp : Nat.card ↥(Subgroup.centralizer {w}) ≠ 0) hk_ne]
      exact Nat.le_add_right _ _
    -- sol centralizer (p ^ v_G) ≡ sol centralizer (p ^ v_C) [MOD p ^ v_C]
    have hmodEq : sol ↥(Subgroup.centralizer {w}) (p ^ (Nat.card G).factorization p)
                  ≡ sol ↥(Subgroup.centralizer {w}) (p ^ (Nat.card ↥(Subgroup.centralizer {w})).factorization p)
                    [MOD p ^ (Nat.card ↥(Subgroup.centralizer {w})).factorization p] :=
      sol_modEq_le hp hv_le
    -- Therefore p ^ v_C divides sol centralizer (p ^ v_G)
    have hdvd_sol : p ^ (Nat.card ↥(Subgroup.centralizer {w})).factorization p
                    ∣ sol ↥(Subgroup.centralizer {w}) (p ^ (Nat.card G).factorization p) := by
      have hiht' : sol ↥(Subgroup.centralizer {w}) (p ^ (Nat.card ↥(Subgroup.centralizer {w})).factorization p) ≡ 0 [MOD p ^ (Nat.card ↥(Subgroup.centralizer {w})).factorization p] := Nat.modEq_zero_iff_dvd.mpr hiht
      exact Nat.modEq_zero_iff_dvd.mp (hmodEq.trans hiht')
    -- Use pPart_dvd_index_mul
    exact pPart_dvd_index_mul hdvd_sol

set_option maxHeartbeats 1000000 in
/-- The induction step for Theorem P. -/
