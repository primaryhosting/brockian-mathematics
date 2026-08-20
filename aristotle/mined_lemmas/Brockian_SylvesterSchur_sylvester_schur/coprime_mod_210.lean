import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma coprime_mod_210 {p : ℕ} (hcop : p.Coprime 210) : (p % 210).Coprime 210 := by
  rw [Nat.Coprime]
  rw [← Nat.gcd_rec 210 p, Nat.gcd_comm 210 p]
  exact hcop

