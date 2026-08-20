/-
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.AKS.Algorithm
import RequestProject.AKS.Cost

/-!
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 8000000

namespace CS

/-- **PRIMES is in P** (Agrawal–Kayal–Saxena).

`AKS.aksBool : ℕ → Bool` is an explicit, fully computable implementation of the AKS primality
test.  On input `n` it checks that `n ≥ 2`, that `n` is not a perfect power, that no `a ≤ r`
shares a nontrivial factor with `n`, and — unless `n ≤ r` — that the congruences
`(X + a)^n = X^n + a` hold in `(ZMod n)[X]/(X^r - 1)` for all `1 ≤ a ≤ ℓ`, where `r = AKS.rAlg n`
is the least modulus for which the multiplicative order of `n` exceeds `(bit length)^4` and
`ℓ = AKS.ellAlg n`.  The congruences are evaluated by repeated squaring in a computable
coefficient-vector model of the quotient ring.

`AKS.aksI : ℕ → Bool × ℕ` is the same algorithm instrumented with a counter: it is a structural
copy of every function involved, threading a count of the primitive operations performed
(see `RequestProject/AKS/Cost.lean` for the cost assigned to each leaf primitive: `r * r`
coefficient multiplications for one cyclic convolution, `bits n` for one `Nat.gcd`, and so on).
Costs are therefore measured in arithmetic operations on numbers of `O(log n)` bits, not in
bit operations.

The statement below records:

* **the instrumented algorithm computes the same answer** as the plain one;
* **correctness**: `AKS.aksBool` decides primality exactly;
* **polynomial running time**: on every input `n ≥ 2` the algorithm performs at most
  `(bit length of n) ^ 45` primitive operations;
* **polynomial size of the parameters**: `r ≤ 2 · (bit length)^12` and `ℓ ≤ 4 · (bit length)^7 + 2`.
-/

theorem isPerfectPower_iff {n : ℕ} (hn : 2 ≤ n) :
    isPerfectPower n = true ↔ ∃ a b : ℕ, 2 ≤ b ∧ n = a ^ b := by
  constructor
  · intro h
    rw [isPerfectPower, List.any_eq_true] at h
    obtain ⟨b, hb, heq⟩ := h
    rw [List.mem_filter] at hb
    have hb2 : 2 ≤ b := by simpa using hb.2
    exact ⟨natRoot b n, b, hb2, (beq_iff_eq.mp heq).symm⟩
  · rintro ⟨a, b, hb, rfl⟩
    have ha : 2 ≤ a := by
      rcases Nat.lt_or_ge a 2 with hlt | hge
      · interval_cases a
        · rw [zero_pow (by omega : b ≠ 0)] at hn; omega
        · rw [one_pow] at hn; omega
      · exact hge
    have hblt : b < bits (a ^ b) := by
      have h1 : (2:ℕ) ^ b ≤ a ^ b := Nat.pow_le_pow_left ha b
      have h2 : a ^ b < 2 ^ bits (a ^ b) := Nat.lt_size_self _
      have : (2:ℕ) ^ b < 2 ^ bits (a ^ b) := lt_of_le_of_lt h1 h2
      exact (Nat.pow_lt_pow_iff_right (by omega)).mp this
    rw [isPerfectPower, List.any_eq_true]
    refine ⟨b, ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨List.mem_range.mpr (by omega), by simpa using hb⟩
    · simp [natRoot_eq (by omega : 1 ≤ b) (rfl : a ^ b = a ^ b)]

end AKS

/-
The AKS algorithm as an explicit computable boolean-valued procedure, together with a proof
that it decides primality.
-/
import Mathlib
import RequestProject.AKS.Defs
import RequestProject.AKS.Complete
import RequestProject.AKS.RBound
import RequestProject.AKS.Quot
import RequestProject.AKS.Compute

open Polynomial

namespace AKS

/-! ### The modulus `r` is computable -/

