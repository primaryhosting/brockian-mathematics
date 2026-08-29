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

theorem spreadDisjoint_of_colourEstimate {B : ℝ} (hB : 1 ≤ B) (h : ColourEstimate (α := α) B) :
    SpreadDisjoint (α := α) (rhoLog (2 * B)) := by
  have hC2 : (2 : ℝ) ≤ 2 * B := by linarith
  intro p k hp hk S hS hspread hcard
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · -- `k = 1`: distinct singletons are pairwise disjoint
    subst hk1
    have hpS : p ≤ S.card := by
      have : (p : ℝ) ≤ (S.card : ℝ) := by
        calc (p : ℝ) ≤ rhoLog (2 * B) p 1 := le_rhoLog _ hC2 p 1 le_rfl
          _ = (rhoLog (2 * B) p 1) ^ 1 := (pow_one _).symm
          _ ≤ (S.card : ℝ) := hcard
      exact_mod_cast this
    obtain ⟨D, hDS, hDcard⟩ := Finset.exists_subset_card_eq hpS
    refine ⟨D, hDS, hDcard, ?_⟩
    intro A hA C hC hAC
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (hS A (hDS hA))
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp (hS C (hDS hC))
    simp only [Finset.disjoint_singleton]
    simpa using hAC
  · -- `k ≥ 2`: colour the ground set with `2p` colours
    have hm : 2 ≤ 2 * p := by omega
    have hmpos : 0 < 2 * p := by omega
    have hSX : ∀ A ∈ S, A ⊆ S.biUnion id := fun A hA a ha =>
      Finset.mem_biUnion.mpr ⟨A, hA, ha⟩
    have hrho : B * ((2 * p : ℕ) : ℝ) * Real.log ((k : ℝ) + 1) = rhoLog (2 * B) p k := by
      simp only [rhoLog, Nat.cast_mul, Nat.cast_ofNat]
      ring
    have hest := h k (2 * p) hk2 hm (S.biUnion id) S hSX hS
      (by rw [hrho]; exact hspread) (by rw [hrho]; exact hcard)
    -- linearity of expectation over the `2p` colour classes
    set X : Finset α := S.biUnion id with hX
    set P : Finset (∀ a ∈ X, Fin (2 * p)) := colorings X (2 * p) with hP
    have hswap : ∑ i : Fin (2 * p), (P.filter (fun f => ∃ A ∈ S, A ⊆ colorClass X f i)).card
        = ∑ f ∈ P, (Finset.univ.filter (fun i : Fin (2 * p) =>
            ∃ A ∈ S, A ⊆ colorClass X f i)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    have hbig : (2 * p) * P.card <
        2 * ∑ i : Fin (2 * p), (P.filter (fun f => ∃ A ∈ S, A ⊆ colorClass X f i)).card := by
      have hne : (Finset.univ : Finset (Fin (2 * p))).Nonempty := by
        refine ⟨⟨0, hmpos⟩, Finset.mem_univ _⟩
      have := Finset.sum_lt_sum_of_nonempty hne
        (fun i _ => hest i)
      simpa [Finset.sum_const, Finset.card_univ, Finset.mul_sum, mul_comm] using this
    -- hence some colouring has more than `p` good colour classes
    have hexf : ∃ f ∈ P, p < (Finset.univ.filter (fun i : Fin (2 * p) =>
        ∃ A ∈ S, A ⊆ colorClass X f i)).card := by
      by_contra hcon
      push_neg at hcon
      have hle : ∑ f ∈ P, (Finset.univ.filter (fun i : Fin (2 * p) =>
          ∃ A ∈ S, A ⊆ colorClass X f i)).card ≤ P.card * p := by
        simpa [smul_eq_mul] using Finset.sum_le_card_nsmul P _ p hcon
      rw [hswap] at hbig
      have h2 : 2 * ∑ f ∈ P, (Finset.univ.filter (fun i : Fin (2 * p) =>
          ∃ A ∈ S, A ⊆ colorClass X f i)).card ≤ (2 * p) * P.card := by
        calc 2 * ∑ f ∈ P, (Finset.univ.filter (fun i : Fin (2 * p) =>
                ∃ A ∈ S, A ⊆ colorClass X f i)).card
            ≤ 2 * (P.card * p) := Nat.mul_le_mul_left 2 hle
          _ = (2 * p) * P.card := by ring
      exact absurd hbig (not_lt.mpr h2)
    obtain ⟨f, -, hf⟩ := hexf
    obtain ⟨G, hGsub, hGcard⟩ :=
      Finset.exists_subset_card_eq (le_of_lt hf)
    have hgood : ∀ i ∈ G, ∃ A, A ∈ S ∧ A ⊆ colorClass X f i := by
      intro i hi
      have := hGsub hi
      rw [Finset.mem_filter] at this
      obtain ⟨A, hAS, hAsub⟩ := this.2
      exact ⟨A, hAS, hAsub⟩
    choose g hgS hgsub using hgood
    have hgne : ∀ (i : Fin (2 * p)) (hi : i ∈ G), (g i hi).Nonempty := by
      intro i hi
      rw [← Finset.card_pos, hS _ (hgS i hi)]
      omega
    have hginj : ∀ (i : Fin (2 * p)) (hi : i ∈ G) (j : Fin (2 * p)) (hj : j ∈ G),
        g i hi = g j hj → i = j := by
      intro i hi j hj hij
      by_contra hne
      obtain ⟨a, ha⟩ := hgne i hi
      have h1 : a ∈ colorClass X f i := hgsub i hi ha
      have h2 : a ∈ colorClass X f j := hgsub j hj (hij ▸ ha)
      exact (Finset.disjoint_left.mp (colorClass_disjoint hne) h1) h2
    refine ⟨G.attach.image (fun i => g i.1 i.2), ?_, ?_, ?_⟩
    · intro A hA
      rw [Finset.mem_image] at hA
      obtain ⟨i, -, rfl⟩ := hA
      exact hgS i.1 i.2
    · rw [Finset.card_image_of_injOn, Finset.card_attach, hGcard]
      intro i _ j _ hij
      exact Subtype.ext (hginj i.1 i.2 j.1 j.2 hij)
    · intro A hA C hC hAC
      rw [Finset.mem_image] at hA hC
      obtain ⟨i, -, rfl⟩ := hA
      obtain ⟨j, -, rfl⟩ := hC
      have hij : i.1 ≠ j.1 := by
        intro hEq
        apply hAC
        cases i; cases j; subst hEq; rfl
      exact Finset.disjoint_of_subset_left (hgsub i.1 i.2)
        (Finset.disjoint_of_subset_right (hgsub j.1 j.2) (colorClass_disjoint hij))

/-- **The improved sunflower bound of Alweiss–Lovett–Wu–Zhang** (in the sharpened form of
Rao and Bell–Chueluecha–Warnke): there is a constant `C` such that every family of more than
`(C * p * log k) ^ k` sets of size `k` contains a sunflower with `p` petals.

The proof formalised here is the Bell–Chueluecha–Warnke derivation: the combinatorial induction
on `k` reducing the bound to the spread case (`sunflower_of_spreadDisjoint`), together with the
random colouring argument (`spreadDisjoint_of_colourEstimate`). Its single input is the
probabilistic estimate `ColourEstimate B` of Alweiss–Lovett–Wu–Zhang / Rao. -/
