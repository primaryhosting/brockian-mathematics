import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# MOD_p is not approximable by low degree functions over a field of characteristic q

This is the second half of Smolensky's argument: if the function `x ↦ ζ^{|x|}`
(`ζ` a primitive `p`-th root of unity in a field `F` of characteristic `q`) agrees
with a function of degree `D` on a set `G` of inputs, then `G` is small.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- The monomial `∏_{i ∈ S} ζ^{x_i}` in the transformed variables. -/

theorem or_gate {q ℓ k D : ℕ} (hq : q.Prime) [CharP F q]
    (g : Fin k → (Fin n → Bool) → F) (hg : ∀ i, g i ∈ LD F n D)
    (bl : Fin k → (Fin n → Bool) → Bool) (E : Finset (Fin n → Bool))
    (hE : ∀ x ∉ E, ∀ i, g i x = bv F (bl i x)) :
    ∃ f ∈ LD F n (ℓ * ((q - 1) * D)),
      2 ^ ℓ * ((univ : Finset (Fin n → Bool)).filter
          (fun x => f x ≠ bv F (decide (∃ i, bl i x = true)))).card
        ≤ 2 ^ ℓ * E.card + 2 ^ n := by
  classical
  have hq2 := hq.two_le
  set Ch : Finset (Fin ℓ → Finset (Fin k)) := univ with hCh
  have hChcard : Ch.card = (2 ^ k) ^ ℓ := by
    simp [hCh, Finset.card_univ, Fintype.card_finset]
  -- the set of inputs where the choice `s` fails, among inputs where all children are correct
  set W : (Fin ℓ → Finset (Fin k)) → Finset (Fin n → Bool) := fun s =>
    (univ : Finset (Fin n → Bool)).filter (fun x => (∃ i, bl i x = true) ∧
      ∀ j, q ∣ (((s j).filter (fun i => bl i x = true)).card)) with hW
  set Bad : (Fin ℓ → Finset (Fin k)) → Finset (Fin n → Bool) := fun s =>
    (univ : Finset (Fin n → Bool)).filter
      (fun x => orApprox q g s x ≠ bv F (decide (∃ i, bl i x = true))) with hBad
  have hsub : ∀ s, Bad s ⊆ E ∪ W s := by
    intro s x hx
    simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    by_contra hcon
    simp only [Finset.mem_union, not_or] at hcon
    obtain ⟨hxE, hxW⟩ := hcon
    refine hx ?_
    refine orApprox_correct hq g s x (fun i => bl i x) (hE x hxE) ?_
    intro i0 hi0
    by_contra hj
    push_neg at hj
    refine hxW ?_
    simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨i0, hi0⟩, hj⟩
  -- pointwise bound on the number of bad choices
  have hpoint : ∀ x : Fin n → Bool,
      2 ^ ℓ * (Ch.filter (fun s => x ∈ W s)).card ≤ Ch.card := by
    intro x
    by_cases hex : ∃ i, bl i x = true
    · obtain ⟨i0, hi0⟩ := hex
      set A : Finset (Finset (Fin k)) := (univ : Finset (Finset (Fin k))).filter
        (fun S => q ∣ ((S.filter fun i => bl i x = true).card)) with hAdef
      have hsubA : (Ch.filter (fun s => x ∈ W s)) ⊆ Fintype.piFinset (fun _ : Fin ℓ => A) := by
        intro s hs
        simp only [Finset.mem_filter, hW, Finset.mem_univ, true_and] at hs
        exact Fintype.mem_piFinset.2 fun j => by
          simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hs.2.2 j
      have hcardA : (Fintype.piFinset (fun _ : Fin ℓ => A)).card = A.card ^ ℓ := by
        rw [Fintype.card_piFinset]; simp
      have h2A : 2 * A.card ≤ 2 ^ k := card_subsets_dvd_le hq2 (fun i => bl i x) i0 hi0
      calc 2 ^ ℓ * (Ch.filter (fun s => x ∈ W s)).card
          ≤ 2 ^ ℓ * A.card ^ ℓ := by
            exact Nat.mul_le_mul_left _ (by
              rw [← hcardA]; exact Finset.card_le_card hsubA)
        _ = (2 * A.card) ^ ℓ := by rw [mul_pow]
        _ ≤ (2 ^ k) ^ ℓ := Nat.pow_le_pow_left h2A ℓ
        _ = Ch.card := hChcard.symm
    · have : (Ch.filter (fun s => x ∈ W s)) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun s _ => ?_
        simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro h
        exact absurd h hex
      simp [this]
  -- sum over all choices
  have hswap : ∑ s ∈ Ch, (W s).card = ∑ x : Fin n → Bool, (Ch.filter (fun s => x ∈ W s)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.card_eq_sum_ones]
    simp only [hW, Finset.sum_filter]
    exact Finset.sum_congr rfl fun x _ => by
      by_cases h : (∃ i, bl i x = true) ∧ ∀ j, q ∣ (((s j).filter (fun i => bl i x = true)).card)
        <;> simp [h]
  have hsum : 2 ^ ℓ * ∑ s ∈ Ch, (W s).card ≤ 2 ^ n * Ch.card := by
    rw [hswap, Finset.mul_sum]
    calc ∑ x : Fin n → Bool, 2 ^ ℓ * (Ch.filter (fun s => x ∈ W s)).card
        ≤ ∑ _x : Fin n → Bool, Ch.card := Finset.sum_le_sum fun x _ => hpoint x
      _ = 2 ^ n * Ch.card := by
          simp [Finset.card_univ]
  have htotal : ∑ s ∈ Ch, (2 ^ ℓ * (Bad s).card) ≤ ∑ _s ∈ Ch, (2 ^ ℓ * E.card + 2 ^ n) := by
    have h1 : ∑ s ∈ Ch, (2 ^ ℓ * (Bad s).card) ≤ ∑ s ∈ Ch, (2 ^ ℓ * (E.card + (W s).card)) := by
      refine Finset.sum_le_sum fun s _ => Nat.mul_le_mul_left _ ?_
      exact (Finset.card_le_card (hsub s)).trans (Finset.card_union_le _ _)
    refine h1.trans ?_
    have h2 : ∑ s ∈ Ch, (2 ^ ℓ * (E.card + (W s).card))
        = Ch.card * (2 ^ ℓ * E.card) + 2 ^ ℓ * ∑ s ∈ Ch, (W s).card := by
      simp [Finset.mul_sum, Nat.mul_add, Finset.sum_add_distrib, mul_comm]
    rw [h2, Finset.sum_const, smul_eq_mul, Nat.mul_add]
    exact Nat.add_le_add_left (hsum.trans (by rw [mul_comm])) _
  have hne : Ch.Nonempty := ⟨fun _ => ∅, Finset.mem_univ _⟩
  obtain ⟨s, -, hs⟩ := Finset.exists_le_of_sum_le hne htotal
  exact ⟨orApprox q g s, orApprox_mem g hg s, hs⟩

/-- The same for an AND gate, by De Morgan. -/
