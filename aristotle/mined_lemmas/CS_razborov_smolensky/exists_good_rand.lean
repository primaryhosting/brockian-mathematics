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


theorem exists_good_rand (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) [Fact q.Prime]
    [CharP F q] :
    ∃ ρ : Rand C t,
      (univ.filter (fun x => gpoly F C q t ρ C.out x ≠ ind F (C.eval q x))).card * 2 ^ t
        ≤ C.size * 2 ^ n := by
  have hx : ∀ x : Fin n → Bool,
      (univ.filter (fun ρ : Rand C t =>
        gpoly F C q t ρ C.out x ≠ ind F (C.eval q x))).card * 2 ^ t
        ≤ C.size * Fintype.card (Rand C t) := by
    intro x
    have hsub : (univ.filter (fun ρ : Rand C t =>
          gpoly F C q t ρ C.out x ≠ ind F (C.eval q x)))
        ⊆ (univ : Finset (Fin C.size)).biUnion
            (fun i => univ.filter (fun ρ : Rand C t => ¬ LocalGood F C q t ρ x i)) := by
      intro ρ hρ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ
      by_contra hc
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      push_neg at hc
      exact hρ (all_good F C q t ρ x (fun i => hc i) C.out)
    calc (univ.filter (fun ρ : Rand C t =>
            gpoly F C q t ρ C.out x ≠ ind F (C.eval q x))).card * 2 ^ t
        ≤ ((univ : Finset (Fin C.size)).biUnion
            (fun i => univ.filter (fun ρ : Rand C t =>
              ¬ LocalGood F C q t ρ x i))).card * 2 ^ t :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
      _ ≤ (∑ i : Fin C.size,
            (univ.filter (fun ρ : Rand C t => ¬ LocalGood F C q t ρ x i)).card) * 2 ^ t :=
          Nat.mul_le_mul_right _ (Finset.card_biUnion_le)
      _ = ∑ i : Fin C.size,
            ((univ.filter (fun ρ : Rand C t => ¬ LocalGood F C q t ρ x i)).card * 2 ^ t) := by
          rw [Finset.sum_mul]
      _ ≤ ∑ _i : Fin C.size, Fintype.card (Rand C t) :=
          Finset.sum_le_sum (fun i _ => card_localbad_le F C q t x i)
      _ = C.size * Fintype.card (Rand C t) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hswap : ∑ x : Fin n → Bool, (univ.filter (fun ρ : Rand C t =>
        gpoly F C q t ρ C.out x ≠ ind F (C.eval q x))).card
      = ∑ ρ : Rand C t, (univ.filter (fun x : Fin n → Bool =>
        gpoly F C q t ρ C.out x ≠ ind F (C.eval q x))).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hmain : ∑ ρ : Rand C t, ((univ.filter (fun x : Fin n → Bool =>
        gpoly F C q t ρ C.out x ≠ ind F (C.eval q x))).card * 2 ^ t)
      ≤ ∑ _ρ : Rand C t, (C.size * 2 ^ n) := by
    rw [← Finset.sum_mul, ← hswap, Finset.sum_mul]
    calc ∑ x : Fin n → Bool, ((univ.filter (fun ρ : Rand C t =>
            gpoly F C q t ρ C.out x ≠ ind F (C.eval q x))).card * 2 ^ t)
        ≤ ∑ _x : Fin n → Bool, (C.size * Fintype.card (Rand C t)) :=
          Finset.sum_le_sum (fun x _ => hx x)
      _ = 2 ^ n * (C.size * Fintype.card (Rand C t)) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          simp
      _ = Fintype.card (Rand C t) * (C.size * 2 ^ n) := by ring
      _ = ∑ _ρ : Rand C t, (C.size * 2 ^ n) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  obtain ⟨ρ, -, hρ⟩ := exists_le_of_sum_le (Finset.univ_nonempty (α := Rand C t)) hmain
  exact ⟨ρ, hρ⟩

/-- Razborov's approximation lemma. -/
