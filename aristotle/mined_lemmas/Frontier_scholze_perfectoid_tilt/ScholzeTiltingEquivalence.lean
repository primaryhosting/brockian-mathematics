/-
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to come first in a file, so the header above uses the plain
-- block-comment delimiter `/-`; the identical text is repeated below as a module docstring.)
import Mathlib

/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

universe u

namespace Frontier

/-!
## The statement

A *perfectoid field* is a complete, non-archimedean valued field `K` of rank one whose value
group is non-discrete and for which the Frobenius map is surjective on `𝒪_K / p`.  Scholze's
tilting construction attaches to such a `K` a perfectoid field `K♭` of characteristic `p`,
whose underlying multiplicative monoid is the inverse limit
`lim_{x ↦ xᵖ} K = { f : ℕ → K | f (n+1) ^ p = f n }` (Mathlib's `Monoid.perfection K p`),
and whose valuation is transported along the "sharp" map `f ↦ f 0`.

`TiltData` below packages exactly this data, and `ScholzeTiltingEquivalence` is the
resulting general statement.  The theorem `Frontier.scholze_perfectoid_tilt` proves the base
case of the equivalence: in equal characteristic `p` the tilt of `K` is `K` itself, the
tilting bijection being `x ↦ (x^{p^{-n}})ₙ`, whose sharp map is the identity.
-/

/-- A `Valued` field `(K, v)` with values in `ℝ≥0` is *perfectoid* for the prime `p` if it is
complete, its valuation is non-trivial with non-discrete (dense) value group, and Frobenius is
surjective on `𝒪_K/p`, the latter being expressed element-wise:
every `x` with `v x ≤ 1` is congruent to a `p`-th power modulo `p`. -/
structure IsPerfectoidField (p : ℕ) (K : Type u) [Field K] [Valued K ℝ≥0] : Prop where
  /-- `p` is a prime number. -/
  prime : p.Prime
  /-- `K` is complete for the valuation topology. -/
  complete : CompleteSpace K
  /-- The valuation is non-trivial. -/
  nontrivial_valuation : ∃ x : K, Valued.v x ≠ 0 ∧ Valued.v x < 1
  /-- The value group is non-discrete. -/
  dense_valuation : ∀ x : K, Valued.v x < 1 → ∃ y : K, Valued.v x < Valued.v y ∧ Valued.v y < 1
  /-- Frobenius is surjective on `𝒪_K/p`. -/
  frobenius_surjective_mod_p : ∀ x : K, Valued.v x ≤ 1 →
    ∃ y : K, Valued.v y ≤ 1 ∧ Valued.v (x - y ^ p) ≤ Valued.v (p : K)

/-- The data of a *tilt* of a valued field `K`: a perfectoid field `K♭` of characteristic `p`
together with a multiplicative bijection `K♭ ≃ lim_{x ↦ xᵖ} K` under which the valuation of
`K♭` is the valuation of the sharp map `f ↦ f 0`. -/
structure TiltData (p : ℕ) (K : Type u) [Field K] [Valued K ℝ≥0] where
  /-- The underlying field of the tilt. -/
  carrier : Type u
  [field : Field carrier]
  [valued : Valued carrier ℝ≥0]
  /-- The tilt has characteristic `p`. -/
  charP : CharP carrier p
  /-- The tilt is again a perfectoid field. -/
  perfectoid : IsPerfectoidField p carrier
  /-- Multiplicatively, the tilt is the inverse limit of `K` along `x ↦ xᵖ`. -/
  toPerfection : carrier ≃* Monoid.perfection K p
  /-- The valuation on the tilt is the valuation of the sharp map. -/
  val_sharp : ∀ x : carrier, Valued.v ((toPerfection x : ℕ → K) 0) = Valued.v x

/-- Scholze's tilting theorem for perfectoid fields, as a statement: every perfectoid field
admits a tilt in the sense of `TiltData`. -/

def ScholzeTiltingEquivalence (p : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] [Valued K ℝ≥0], IsPerfectoidField p K → Nonempty (TiltData p K)

/-!
## The base case: equal characteristic `p`
-/

/-- A perfectoid field of characteristic `p` is perfect: Frobenius is surjective. -/
