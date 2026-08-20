/-
  Brockian/SieveHamiltonian.lean — THE SIEVE HAMILTONIAN CAMPAIGN
  (July 30, after the "invent the dynamics" program note).

  The object: on the arithmetic wheel Z/M (M odd squarefree), the twin
  sieve deletes residues a with a ≡ 0 or a ≡ −2 mod some ℓ ∣ M. Once
  3 ∣ M the admissible set is pinned to the coset a ≡ 2 (mod 3); the
  residual translation flow is +3 on that coset. The compressed
  Hamiltonian (Dirichlet deletion of forbidden sites from the residual
  cycle) decomposes into path Laplacians over the admissible RUNS, so
  its spectrum is exact and finite. Everything below is finite; no
  Hilbert–Pólya claim is made anywhere in this file — the operator
  limit M → ∞ is an OPEN PROGRAM subject to the G0–G6 gate ladder.

  Charter as Core.lean. The declarations below are the formal campaign targets.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.SieveHamiltonian

open Matrix

/-! ## 1. The no-go theorem: why the naive adjacency dies at 3 -/

/-- Twin admissibility pins the mod-3 residue. -/

theorem tripleAdmissibleCount_squarefree (M : ℕ)
    (hM : Squarefree M) (hodd : Odd M) :
    tripleAdmissibleCount M =
      ∏ p ∈ M.primeFactors,
        (if p = 3 ∨ p = 5 then 1 else p - 6) := by
  have h : ∀ n : ℕ, Squarefree n → Odd n →
    tripleAdmissibleCount n = ∏ p ∈ n.primeFactors, (if p = 3 ∨ p = 5 then 1 else p - 6) := by
    intro n hn_sq hn_odd
    exact Nat.strong_induction_on n (fun m ih hm_sq hm_odd => by
      by_cases hm1 : m = 1
      · subst hm1
        simp [tripleAdmissibleCount]
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨?_, ?_⟩
        · infer_instance
        · refine ⟨0, ?_⟩
          simp [TripleAdmissible]
          trivial
      · -- m > 1, so m has at least one prime factor
        have hm_gt1 : 1 < m := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨fun h => by simp [h] at hm_sq, hm1⟩
        have hp : m.minFac.Prime := Nat.minFac_prime hm_gt1.ne'
        have hpdvd : m.minFac ∣ m := Nat.minFac_dvd m
        -- Set p = m.minFac and q = m / p
        set p := m.minFac with hp_def
        set q := m / p with hq_def
        have hmp : m = p * q := (Nat.mul_div_cancel' hpdvd).symm
        have hq_lt : q < m := Nat.div_lt_self (by omega) hp.one_lt
        have hq_sq : Squarefree q := hm_sq.squarefree_of_dvd (Nat.div_dvd_of_dvd hpdvd)
        have hq_odd : Odd q := hm_odd.of_dvd_nat (Nat.div_dvd_of_dvd hpdvd)
        -- p and q are coprime since m is squarefree
        have hp_coprime_q : Nat.Coprime p q := by
          rw [hp.coprime_iff_not_dvd]
          intro hdvd
          have : p ^ 2 ∣ m := by
            calc p ^ 2 = p * p := by ring
              _ ∣ p * q := Nat.mul_dvd_mul_left p hdvd
              _ = m := hmp.symm
          have hnsq : ¬ Squarefree (p ^ 2) := by
            intro hsq
            rw [Squarefree] at hsq
            specialize hsq p
            simp [pow_two] at hsq
            exact hp.ne_one hsq
          exact absurd (hm_sq.squarefree_of_dvd this) hnsq
        -- Rewrite m = p * q
        rw [hmp]
        -- Use multiplicativity
        rw [tripleAdmissibleCount_mul_of_coprime p q hp_coprime_q]
        -- p is odd since m is odd
        have hp_odd : Odd p := hm_odd.of_dvd_nat hpdvd
        -- Use the prime case for p
        rw [tripleAdmissibleCount_prime p hp hp_odd]
        -- Use induction hypothesis for q
        rw [ih q hq_lt hq_sq hq_odd]
        -- p ∉ q.primeFactors since p and q are coprime
        have hp_not_in_q : p ∉ q.primeFactors := by
          intro h
          have hdiv : p ∣ q := Nat.mem_primeFactors.mp h |>.2.1
          rw [Nat.Coprime] at hp_coprime_q
          have := Nat.dvd_gcd (dvd_refl p) hdiv
          simp [hp_coprime_q] at this
          exact hp.ne_one this
        have hq_ne_zero : q ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (by omega) hpdvd) hp.pos)
        rw [Nat.primeFactors_mul hp.ne_zero hq_ne_zero]
        rw [hp.primeFactors]
        rw [Finset.prod_union (Finset.disjoint_singleton_left.mpr hp_not_in_q)]
        simp) hn_sq hn_odd
  exact h M hM hodd

