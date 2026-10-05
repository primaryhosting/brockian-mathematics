import Mathlib
/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

namespace Brockian

variable {n : ℕ} [NeZero n]

/-- The `k`-th character of the vertex set `ZMod n` of the regular `n`-gon:
`χ_k(j) = exp (2πi k j / n)`. -/

noncomputable def ngonProj (n : ℕ) [NeZero n] (k : ZMod n) (f : ZMod n → ℂ) : ZMod n → ℂ :=
  fun j => (n : ℂ)⁻¹ * ∑ m : ZMod n, ngonChar n k (j - m) * f m

/-- The Fourier coefficient of `f` at the character `χ_k`. -/
