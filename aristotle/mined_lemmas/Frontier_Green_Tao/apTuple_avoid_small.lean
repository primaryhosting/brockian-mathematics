import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to appear before any other
command in a module, including module docstrings, so the mandated header comment appears
immediately after the single `import Mathlib` line.
-/

open scoped BigOperators

namespace Frontier

/-- `PrimeAP k` says that there is an arithmetic progression of length `k` with positive
common difference all of whose terms are prime. -/

lemma apTuple_avoid_small {k p : ℕ} (hp : p.Prime) (hpk : p ≤ k) :
    ∀ b ∈ apTuple k, ¬ (p ∣ 1 + b) := by
  intro b hb
  rcases mem_apTuple.mp hb with ⟨i, _, rfl⟩
  have hdvd : p ∣ Nat.factorial k := hp.dvd_factorial.mpr hpk
  intro hcon
  have h1 : p ∣ i * Nat.factorial k := Dvd.dvd.mul_left hdvd i
  have : p ∣ 1 := (Nat.dvd_add_right h1).mp (by rwa [Nat.add_comm] at hcon)
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp this)

/-- Large primes: if `p > k` then the `k` residues `-i·k! (mod p)` cannot exhaust the `p`
residue classes, so some shift `n` avoids them all. -/
