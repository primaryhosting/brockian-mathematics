import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem gate_dichotomy_andg (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) [Fact q.Prime]
    [CharP F q] (x : Fin n → Bool) (i : Fin C.size) (S : Finset (Fin i.val))
    (hg : C.gate i = .andg S) :
    (∀ ρ : Rand C t, LocalGood F C q t ρ x i) ∨
    ∃ (S : Finset (Fin i.val)) (w : Fin i.val → Bool) (j₀ : Fin i.val),
      j₀ ∈ S ∧ w j₀ = true ∧
      ∀ ρ : Rand C t, ¬ LocalGood F C q t ρ x i →
        ∀ κ : Fin t, q ∣ (S.filter (fun j => ρ i κ (C.up i j) = true ∧ w j = true)).card := by
  set w : Fin i.val → Bool := fun j => !(C.gval q x (C.up i j)) with hw
  have hmain : ∀ ρ : Rand C t, (∀ j : Fin i.val, Good F C q t ρ x (C.up i j)) →
      gpoly F C q t ρ i x =
        (if (∀ κ : Fin t,
          q ∣ (S.filter (fun j => ρ i κ (C.up i j) = true ∧ w j = true)).card) then 1 else 0) := by
    intro ρ hch
    rw [gpoly_andg F C q t ρ i S hg]
    simp only [Pi.sub_apply, Pi.one_apply, Finset.prod_apply, Pi.pow_apply, Finset.sum_apply]
    refine prod_dvd_eval q S (fun κ j => ρ i κ (C.up i j))
      (fun j => 1 - gpoly F C q t ρ (C.up i j) x) w (fun j _ => ?_)
    dsimp only
    rw [show gpoly F C q t ρ (C.up i j) x = ind F (C.gval q x (C.up i j)) from hch j, ← ind_not]
  by_cases hall : ∀ j ∈ S, w j = false
  · left
    intro ρ hch
    have hallv : ∀ j ∈ S, C.gval q x (C.up i j) = true := by
      intro j hj
      simpa [hw] using hall j hj
    simp only [Good, hmain ρ hch, gval_andg C q x i S hg]
    have hcnt : ∀ κ : Fin t,
        (S.filter (fun j => ρ i κ (C.up i j) = true ∧ w j = true)).card = 0 := by
      intro κ
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j hj
      rw [hall j hj]
      simp
    rw [if_pos (fun κ => by rw [hcnt κ]; exact dvd_zero q)]
    have hinf : S.inf (fun j => C.gval q x (C.up i j)) = true :=
      le_antisymm (by simp) (Finset.le_inf (fun j hj => by rw [hallv j hj]))
    rw [hinf]
    simp [ind]
  · right
    push_neg at hall
    obtain ⟨j₀, hj₀S, hj₀⟩ := hall
    have h2 : w j₀ = true := by simpa [hw] using hj₀
    have h3 : C.gval q x (C.up i j₀) = false := by simpa [hw] using h2
    refine ⟨S, w, j₀, hj₀S, h2, ?_⟩
    intro ρ hbad
    by_contra hcon
    apply hbad
    intro hch
    simp only [Good, hmain ρ hch, gval_andg C q x i S hg, if_neg hcon]
    have hinf : S.inf (fun j => C.gval q x (C.up i j)) = false := by
      have h1 : S.inf (fun j => C.gval q x (C.up i j)) ≤ C.gval q x (C.up i j₀) :=
        Finset.inf_le hj₀S
      rw [h3] at h1
      rcases Bool.eq_false_or_eq_true (S.inf (fun j => C.gval q x (C.up i j))) with hs | hs
      · rw [hs] at h1; exact absurd h1 (by decide)
      · exact hs
    rw [hinf]
    simp [ind]

/-- Either the gate `i` never introduces an error on input `x`, or there is a witness making
the failure event a "all `t` random subsets select a multiple of `q` witnesses" event. -/
