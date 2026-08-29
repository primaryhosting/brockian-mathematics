import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace QI

/-- Bit strings of length `n`, as vectors over the field `ZMod 2`.
Addition is bitwise XOR. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product `⟨x, y⟩ = ⨁ i, x i * y i`. -/

theorem classical_query_lower_bound_exp {n q : ℕ} (hn : 2 ≤ n) (t : DTree n q)
    (hcorrect : ∀ s : BV n, s ≠ 0 → ∀ f, IsSimon s f → t.run f = s) :
    2 ^ ((n - 1) / 2) ≤ q := by
  have h := classical_query_lower_bound t hcorrect
  have h1 : 2 ^ (n - 1) ≤ q * q := by
    have h2 : (2:ℕ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : (2:ℕ) ^ 1 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h4 : 2 ^ ((n - 1) / 2) * 2 ^ ((n - 1) / 2) ≤ 2 ^ (n - 1) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Nat.mul_self_le_mul_self_iff.mp (le_trans h4 h1)

/-- **Simon's problem.**

* (quantum, part 1) every measurement outcome of the quantum algorithm is orthogonal to the
  hidden shift `s` (outcomes `y` with `⟨s,y⟩ = 1` have amplitude `0`);
* (quantum, part 2) all outcomes orthogonal to `s` do occur (nonzero amplitude);
* (quantum, part 3) `n` such linear constraints determine `s`, so `O(n)` quantum queries suffice;
* (classical) every deterministic adaptive classical algorithm that always outputs the hidden
  shift needs `q` queries with `2^n ≤ q^2 + 2`, hence `q ≥ 2^{(n-1)/2} = Ω(2^{n/2})`.
-/
