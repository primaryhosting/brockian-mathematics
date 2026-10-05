/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of sets is a *sunflower with core `c`* if any two distinct members of `S`
intersect exactly in `c`. -/

theorem spreadDisjoint_mul : SpreadDisjoint (α := α) (fun p k => (p : ℝ) * k) := by
  intro p k hp hk S hS hspread hcard
  classical
  simp only at hspread hcard
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hp0 : (0 : ℝ) < p := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hr0 : (0 : ℝ) < (p : ℝ) * k := mul_pos hp0 hk0
  have hpow : ((p : ℝ) * k) ^ k = ((p : ℝ) * k) ^ (k - 1) * ((p : ℝ) * k) := by
    rw [← pow_succ]
    congr 1
    omega
  have hdeg : ∀ x : α, ((S.filter (fun A => x ∈ A)).card : ℝ) ≤ ((p : ℝ) * k) ^ (k - 1) := by
    intro x
    have hx := hspread {x} (Finset.singleton_nonempty x)
    simpa only [Finset.singleton_subset_iff, Finset.card_singleton] using hx
  have key : ∀ i : ℕ, i ≤ p →
      ∃ D ⊆ S, D.card = i ∧ ∀ A ∈ D, ∀ B ∈ D, A ≠ B → Disjoint A B := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨∅, by simp, by simp, by simp⟩
    | succ i ihi =>
      intro hip
      obtain ⟨D, hDS, hDcard, hDdisj⟩ := ihi (by omega)
      have hUcard : ((D.biUnion id).card : ℝ) ≤ (i : ℝ) * k := by
        have h1 : (D.biUnion id).card ≤ ∑ B ∈ D, (id B).card := Finset.card_biUnion_le
        have h2 : ∑ B ∈ D, (id B).card = i * k := by
          have : ∑ B ∈ D, (id B).card = ∑ _B ∈ D, k :=
            Finset.sum_congr rfl (fun B hB => hS B (hDS hB))
          rw [this, Finset.sum_const, hDcard, smul_eq_mul]
        have : (D.biUnion id).card ≤ i * k := by omega
        exact_mod_cast this
      have hex : ∃ A ∈ S, Disjoint A (D.biUnion id) := by
        by_contra hcon
        push_neg at hcon
        have hsub : S ⊆ (D.biUnion id).biUnion (fun x => S.filter (fun A => x ∈ A)) := by
          intro A hA
          obtain ⟨x, hx⟩ := Finset.not_disjoint_iff_nonempty_inter.mp (hcon A hA)
          rw [Finset.mem_inter] at hx
          exact Finset.mem_biUnion.mpr ⟨x, hx.2, Finset.mem_filter.mpr ⟨hA, hx.1⟩⟩
        have h1 : (S.card : ℝ) ≤ ∑ x ∈ D.biUnion id, ((S.filter (fun A => x ∈ A)).card : ℝ) := by
          have hnat : S.card ≤ ∑ x ∈ D.biUnion id, (S.filter (fun A => x ∈ A)).card :=
            le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
          exact_mod_cast hnat
        have h2 : ∑ x ∈ D.biUnion id, ((S.filter (fun A => x ∈ A)).card : ℝ)
            ≤ ((D.biUnion id).card : ℝ) * ((p : ℝ) * k) ^ (k - 1) := by
          calc ∑ x ∈ D.biUnion id, ((S.filter (fun A => x ∈ A)).card : ℝ)
              ≤ ∑ _x ∈ D.biUnion id, ((p : ℝ) * k) ^ (k - 1) :=
                Finset.sum_le_sum (fun x _ => hdeg x)
            _ = ((D.biUnion id).card : ℝ) * ((p : ℝ) * k) ^ (k - 1) := by
                rw [Finset.sum_const, nsmul_eq_mul]
        have hip' : (i : ℝ) ≤ (p : ℝ) - 1 := by
          have : (i : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hip
          linarith
        have hpk : (0 : ℝ) < ((p : ℝ) * k) ^ (k - 1) := by positivity
        have hfinal : (S.card : ℝ) < ((p : ℝ) * k) ^ k := by
          calc (S.card : ℝ) ≤ ((D.biUnion id).card : ℝ) * ((p : ℝ) * k) ^ (k - 1) :=
                le_trans h1 h2
            _ ≤ ((i : ℝ) * k) * ((p : ℝ) * k) ^ (k - 1) := by
                exact mul_le_mul_of_nonneg_right hUcard (le_of_lt hpk)
            _ ≤ (((p : ℝ) - 1) * k) * ((p : ℝ) * k) ^ (k - 1) := by
                have : (i : ℝ) * k ≤ ((p : ℝ) - 1) * k :=
                  mul_le_mul_of_nonneg_right hip' (le_of_lt hk0)
                exact mul_le_mul_of_nonneg_right this (le_of_lt hpk)
            _ < ((p : ℝ) * k) * ((p : ℝ) * k) ^ (k - 1) := by
                have : (((p : ℝ) - 1) * k) < ((p : ℝ) * k) := by nlinarith
                exact mul_lt_mul_of_pos_right this hpk
            _ = ((p : ℝ) * k) ^ k := by rw [hpow]; ring
        linarith
      obtain ⟨A, hAS, hAU⟩ := hex
      have hAne : A.Nonempty := by
        rw [← Finset.card_pos, hS A hAS]
        omega
      have hAD : A ∉ D := by
        intro hAD
        obtain ⟨z, hz⟩ := hAne
        have hzU : z ∈ D.biUnion id := Finset.mem_biUnion.mpr ⟨A, hAD, hz⟩
        exact (Finset.disjoint_left.mp hAU hz) hzU
      refine ⟨insert A D, Finset.insert_subset hAS hDS, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hAD, hDcard]
      · intro X hX Y hY hXY
        have hsubU : ∀ Z ∈ D, Z ⊆ D.biUnion id := fun Z hZ z hz =>
          Finset.mem_biUnion.mpr ⟨Z, hZ, hz⟩
        rcases Finset.mem_insert.mp hX with rfl | hX' <;>
          rcases Finset.mem_insert.mp hY with rfl | hY'
        · exact absurd rfl hXY
        · exact Finset.disjoint_of_subset_right (hsubU Y hY') hAU
        · exact (Finset.disjoint_of_subset_right (hsubU X hX') hAU).symm
        · exact hDdisj X hX' Y hY' hXY
  exact key p le_rfl

/-- The unconditional sunflower bound coming from the greedy spread argument: any family of at
least `(p * k) ^ k` sets of size `k` contains a sunflower with `p` petals. -/
