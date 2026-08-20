import Mathlib
namespace Brockian.MsGaussLucas

open Polynomial

/-- The conjugate of `u⁻¹` is the positive real multiple `(normSq u)⁻¹` of `u`. -/

private lemma exists_linear_factorization (p : ℂ[X]) (hp : p ≠ 0) :
    ∃ (a : ℂ) (r : Fin p.natDegree → ℂ), a ≠ 0 ∧ p = C a * ∏ i, (X - C (r i)) := by
  induction d : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn
      use p.coeff 0
      have hne : p.coeff 0 ≠ 0 := by
        intro h
        apply hp
        rw [Polynomial.eq_C_of_natDegree_eq_zero d]
        simp [h]
      use fun i => 0
      simp [hne]
      exact Polynomial.eq_C_of_natDegree_eq_zero d
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      have hdeg : 0 < p.natDegree := by rw [d]; exact hn'
      -- Find a root of p
      have hdeg' : p.degree ≠ 0 := ne_of_gt (natDegree_pos_iff_degree_pos.mp hdeg)
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hdeg'
      -- (X - r) divides p
      have hdvd : (X - C r) ∣ p := dvd_iff_isRoot.mpr hr
      obtain ⟨q, hq⟩ := hdvd
      -- q ≠ 0
      have hq0 : q ≠ 0 := by
        intro hqz
        rw [hq, hqz, mul_zero] at hp
        exact hp rfl
      -- natDegree q = n - 1
      have hqdeg : q.natDegree = n - 1 := by
        have : p.natDegree = (X - C r).natDegree + q.natDegree := by
          rw [hq]; exact natDegree_mul (X_sub_C_ne_zero r) hq0
        rw [natDegree_X_sub_C] at this
        omega
      -- Apply inductive hypothesis to q
      have ihq := ih (n - 1) (by omega) q hq0 hqdeg
      obtain ⟨a, s, ha, hs⟩ := ihq
      -- Combine into a factorization for p
      have heq : n = n - 1 + 1 := by omega
      have hinv : n - 1 + 1 = n := by omega
      -- Use n - 1 + 1 = n to work with Fin (n - 1 + 1) directly
      have key : ∃ (a : ℂ) (r' : Fin (n - 1 + 1) → ℂ), a ≠ 0 ∧ (X - C r) * q = C a * ∏ i : Fin (n - 1 + 1), (X - C (r' i)) := by
        use a, Fin.cons r s
        refine ⟨ha, ?_⟩
        rw [hs]
        rw [Fin.prod_univ_succ]
        simp [Fin.cons_zero]
        ring
      obtain ⟨a', r', ha', hr'⟩ := key
      use a', r' ∘ Fin.cast heq
      refine ⟨ha', ?_⟩
      rw [hq, hr']
      congr 1
      symm
      apply Finset.prod_bij (fun i _ => Fin.cast heq i)
      · intro i _; simp
      · intro i₁ _ i₂ _ h; exact Fin.cast_injective heq h
      · intro b _; exact ⟨Fin.cast hinv b, by simp⟩
      · intro i _; simp

/-- Logarithmic derivative identity: if `p = C a * ∏ (X - r i)`, `z` is a root of `p.derivative`
and `z` is not a root of `p`, then `∑ (z - r i)⁻¹ = 0`. -/
