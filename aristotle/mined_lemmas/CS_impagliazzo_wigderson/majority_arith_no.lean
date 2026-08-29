/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately written without any `import`, because the required header above is a
module doc comment and Lean does not allow `import` commands after it.  All notions below are
therefore developed from scratch in core Lean 4.

Probabilities over `k` random bits are represented exactly by integer counts: instead of saying
that the acceptance probability is at least `2/3` we say `2 * 2 ^ m ≤ 3 * (number of accepting
random strings)`, and similarly for the other bounds.  This is an exact (not approximate)
reformulation, and it avoids any need for rational arithmetic.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-! ## Strings, languages, algorithms -/

/-- A finite binary string. -/
abbrev Bits := List Bool

/-- A language is a set of binary strings. -/
abbrev Language := Bits → Prop

/-- A randomized algorithm: it reads an input string and a random string, the latter encoded as
a natural number `r < 2 ^ m`, where `m` is the number of random bits used. -/
abbrev RAlgo := Bits → Nat → Bool

/-- A deterministic algorithm. -/
abbrev DAlgo := Bits → Bool

/-- `countUpTo f N` is the number of `r < N` with `f r = true`. -/

theorem majority_arith_no (a b c d : Nat) (hb : 0 < b) (hd : 0 < d)
    (hgap : 3 * a ≤ b) (hfool : 12 * (c * b) ≤ 12 * (a * d) + d * b) : 2 * c ≤ d := by
  have hcomm : d * b = b * d := Nat.mul_comm d b
  have h1 : 12 * a ≤ 4 * b := by omega
  have h2 : (12 * a) * d ≤ (4 * b) * d := Nat.mul_le_mul_right d h1
  have h3 : 12 * (a * d) ≤ 4 * (b * d) := by
    calc 12 * (a * d) = (12 * a) * d := by rw [Nat.mul_assoc]
    _ ≤ (4 * b) * d := h2
    _ = 4 * (b * d) := by rw [Nat.mul_assoc]
  have h4 : 12 * (c * b) ≤ 5 * (b * d) := by omega
  have h5 : (12 * c) * b ≤ (5 * d) * b := by
    calc (12 * c) * b = 12 * (c * b) := by rw [Nat.mul_assoc]
    _ ≤ 5 * (b * d) := h4
    _ = (5 * d) * b := by rw [Nat.mul_assoc, hcomm]
  have h6 : 12 * c ≤ 5 * d := Nat.le_of_mul_le_mul_right h5 hb
  omega

/-- If `A` accepts `x` with probability at least `2/3` and `G` fools `A` on `x`, the majority
vote over the seeds of `G` accepts. -/
