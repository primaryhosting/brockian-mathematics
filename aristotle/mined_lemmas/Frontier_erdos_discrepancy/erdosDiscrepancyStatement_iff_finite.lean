/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is written in plain Lean 4 core (no imports), so that the header comment above
can legally be the very first thing in the file.
-/

namespace Frontier

/-- A `±1` sequence: `f n ∈ {1, -1}` for every index `n ≥ 1`. -/

theorem erdosDiscrepancyStatement_iff_finite :
    ErdosDiscrepancyStatement ↔ ErdosDiscrepancyFinite := by
  constructor
  · -- the hard direction: compactness of Cantor space
    intro H C
    by_contra hN
    push_neg at hN
    -- for each `N`, a `±1` sequence with no witness inside `{1, …, N}`
    have hbad : ∀ N : ℕ, ∃ g : ℕ → Bool, ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → n * d ≤ N →
        (hapSum (boolSeq g) d n).natAbs ≤ C := by
      intro N
      obtain ⟨f, hf, hfbad⟩ := hN N
      obtain ⟨g, hg⟩ := exists_boolSeq_hapSum_eq f hf
      refine ⟨g, fun d n hd hn hnd => ?_⟩
      rw [hg d n hd]
      exact hfbad d n hd hn hnd
    set t : ℕ → Set (ℕ → Bool) := fun N =>
      {g | ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → n * d ≤ N → (hapSum (boolSeq g) d n).natAbs ≤ C}
      with ht
    have hmono : ∀ N : ℕ, t (N + 1) ⊆ t N := by
      intro N g hg d n hd hn hnd
      exact hg d n hd hn (by omega)
    have hne : ∀ N : ℕ, (t N).Nonempty := by
      intro N
      obtain ⟨g, hg⟩ := hbad N
      exact ⟨g, hg⟩
    have hclosed : ∀ N : ℕ, IsClosed (t N) := by
      intro N
      have hrw : t N = ⋂ d : ℕ, ⋂ n : ℕ,
          {g : ℕ → Bool | 1 ≤ d → 1 ≤ n → n * d ≤ N →
            (hapSum (boolSeq g) d n).natAbs ≤ C} := by
        ext g
        simp [ht, Set.mem_iInter]
      rw [hrw]
      refine isClosed_iInter fun d => isClosed_iInter fun n => ?_
      by_cases hyp : 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ N
      · have hset : {g : ℕ → Bool | 1 ≤ d → 1 ≤ n → n * d ≤ N →
              (hapSum (boolSeq g) d n).natAbs ≤ C}
            = (fun g : ℕ → Bool => hapSum (boolSeq g) d n) ⁻¹' {x : ℤ | x.natAbs ≤ C} := by
          ext g
          simp [hyp.1, hyp.2.1, hyp.2.2]
        rw [hset]
        exact (isClosed_discrete _).preimage (continuous_hapSum_boolSeq d n)
      · have hset : {g : ℕ → Bool | 1 ≤ d → 1 ≤ n → n * d ≤ N →
              (hapSum (boolSeq g) d n).natAbs ≤ C} = Set.univ := by
          ext g
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
          intro h1 h2 h3
          exact absurd ⟨h1, h2, h3⟩ hyp
        rw [hset]
        exact isClosed_univ
    obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      t hmono hne (hclosed 0).isCompact hclosed
    obtain ⟨d, n, hd, hn, hlt⟩ := H (boolSeq g) (boolSeq_isPlusMinusOne g) C
    have := Set.mem_iInter.mp hg (n * d) d n hd hn le_rfl
    omega
  · -- the easy direction
    intro H f hf C
    obtain ⟨N, hNs⟩ := H C
    obtain ⟨d, n, hd, hn, _, hlt⟩ := hNs f hf
    exact ⟨d, n, hd, hn, hlt⟩

/-- The `C = 1` instance of the finitary form holds with `N = 12`, by
`Frontier.erdos_discrepancy_uniform`. -/
