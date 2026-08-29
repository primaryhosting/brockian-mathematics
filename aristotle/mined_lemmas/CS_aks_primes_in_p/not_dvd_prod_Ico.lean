import Mathlib

/-!
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Finset

namespace CS

/-- For `q` a prime factor of `n` with `q < n`, the product `∏_{i=1}^{q-1} (n - i)`
is not divisible by `q`. -/

lemma not_dvd_prod_Ico {n q : ℕ} (hq : q.Prime) (hqn : q ∣ n) (hlt : q < n) :
    ¬ q ∣ ∏ i ∈ Finset.Ico 1 q, (n - i) := by
  intro h
  obtain ⟨i, hi, hdvd⟩ := hq.prime.exists_mem_finset_dvd h
  simp only [Finset.mem_Ico] at hi
  have hin : i < n := lt_trans hi.2 hlt
  have hqi : q ∣ i := by
    have h' : i = n - (n - i) := by omega
    rw [h']
    exact Nat.dvd_sub hqn hdvd
  have := Nat.le_of_dvd (by omega) hqi
  omega

/-- The `q`-adic valuation of `n.choose q` is one less than that of `n`,
when `q` is a prime factor of `n` with `q < n`. -/
