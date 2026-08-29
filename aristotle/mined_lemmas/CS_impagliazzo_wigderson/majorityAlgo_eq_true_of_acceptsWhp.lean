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

theorem majorityAlgo_eq_true_of_acceptsWhp (A : RAlgo) (G : Nat → Nat → Nat) (x : Bits)
    (m s : Nat → Nat) (hacc : AcceptsWhp A x (m x.length))
    (hfool : Fools A G x (m x.length) (s x.length)) : majorityAlgo A G s x = true := by
  have := majority_arith_yes (acceptCount A x (m x.length)) (2 ^ (m x.length))
    (genAcceptCount A G x (s x.length)) (2 ^ (s x.length))
    (two_pow_pos _) (two_pow_pos _) hacc hfool.1
  simpa [majorityAlgo] using this

/-- If `A` accepts `x` with probability at most `1/3` and `G` fools `A` on `x`, the majority vote
over the seeds of `G` rejects. -/
