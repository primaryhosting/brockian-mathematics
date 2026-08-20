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

theorem triple_count (M : ℕ) (hM : Squarefree M) (h3 : 3 ∣ M) (h5 : 5 ∣ M)
    (hodd : Odd M) :
    Nat.card {a : ZMod M //
        IsUnit (a * (a + 2)) ∧ IsUnit ((a + 3) * (a + 5)) ∧
        IsUnit ((a + 6) * (a + 8))} =
      ∏ ℓ ∈ M.primeFactors.filter (7 ≤ ·), (ℓ - 6) := by
  have eq1 := tripleAdmissibleCount_squarefree M hM hodd
  unfold tripleAdmissibleCount at eq1
  simp only [TripleAdmissible] at eq1
  rw [eq1]
  -- The RHS uses filter, let's rewrite to match
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hne2 : p ≠ 2 := by
    intro h
    rw [h] at hp
    have hdvd : 2 ∣ M := Nat.dvd_of_mem_primeFactors hp
    exact Nat.not_even_iff_odd.mpr hodd (Nat.even_iff.mpr (by omega : M % 2 = 0))
  split_ifs
  · -- p = 3 ∨ p = 5, 7 ≤ p → contradiction
    exfalso; clear eq1 h3 h5 hodd hM hp hprime hne2; omega
  · -- p = 3 ∨ p = 5, ¬7 ≤ p → 1 = 1
    rfl
  · -- ¬(p = 3 ∨ p = 5), 7 ≤ p → p - 6 = p - 6
    rfl
  · -- ¬(p = 3 ∨ p = 5), ¬7 ≤ p → contradiction
    exfalso
    clear eq1 h3 h5 hodd hM hp
    have hp2 : p ≥ 2 := hprime.two_le
    have hp3 : p ≠ 3 := fun h => ‹¬(p = 3 ∨ p = 5)› (Or.inl h)
    have hp5 : p ≠ 5 := fun h => ‹¬(p = 3 ∨ p = 5)› (Or.inr h)
    have hp7 : p < 7 := not_le.mp ‹_›
    interval_cases p <;> simp_all (config := {decide := true})

end Brockian.SieveHamiltonian

