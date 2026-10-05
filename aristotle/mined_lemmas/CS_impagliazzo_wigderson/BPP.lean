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

def BPP (L : Language) : Prop :=
  ∃ (A : RAlgo) (m : Nat → Nat), M.RandPoly A ∧ M.IsPoly m ∧ ∀ x,
    (L x → AcceptsWhp A x (m x.length)) ∧ (¬ L x → RejectsWhp A x (m x.length))

/-- The hardness-to-randomness conclusion of the Nisan–Wigderson construction, as used by
Impagliazzo and Wigderson: every randomized polynomial-time algorithm is fooled, on every input,
by a polynomial-time computable generator whose seed length is logarithmic, i.e. which has only
polynomially many seeds. -/
