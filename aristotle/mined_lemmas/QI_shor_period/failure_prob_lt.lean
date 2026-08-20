import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

/-- The modular exponentiation function `k ↦ a ^ k mod n`, the function whose period
Shor's algorithm computes. -/

lemma failure_prob_lt {p : ℝ} (hp : 0 < p) {eps : ℝ} (heps : 0 < eps) :
    ∃ t : ℕ, (1 - p) ^ t < eps :=
  exists_pow_lt_of_lt_one heps (by linarith)

/--
**Shor's period finding.**

Let `n > 1` and let `a` be coprime to `n`, and let `r` be the order of `a` modulo `n`.
Then:

1. `r > 0` and `r` is a period of the modular exponentiation function `k ↦ a ^ k mod n`;
2. `r` is the *minimal* period, and in fact the periods are exactly the multiples of `r`;
3. (recovery) a measurement outcome giving the exact rational `s / r` with `s` coprime to
   `r` determines `r`: the denominator of `s / r` in lowest terms is `r`.  This is the
   continued-fraction post-processing step of Shor's algorithm;
4. (with high probability) the number of good outcomes `s < r` is `φ r`, so a single run
   succeeds with probability `φ r / r > 0`, and hence for any `ε > 0` there is a number of
   independent repetitions `t` after which the failure probability `(1 - φ r / r) ^ t` is
   below `ε`; i.e. the period is recovered with probability arbitrarily close to `1`.
-/
