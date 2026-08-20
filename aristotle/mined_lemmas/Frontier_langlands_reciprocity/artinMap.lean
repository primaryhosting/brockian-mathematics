import Mathlib

/-!
# Langlands Reciprocity
Category: Frontier Abel
Target: Frontier.langlands_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Frontier

open Polynomial IsCyclotomicExtension

variable (n : ℕ) [NeZero n] (L : Type*) [Field L] [Algebra ℚ L]
  [IsCyclotomicExtension {n} ℚ L]

/-- **The Artin reciprocity map** for the cyclotomic extension `ℚ(ζ_n)/ℚ`:
the isomorphism from the idele class group of conductor `n`, namely `(ZMod n)ˣ`,
onto the Galois group `Gal(ℚ(ζ_n)/ℚ)`. -/

noncomputable def artinMap : (ZMod n)ˣ ≃* (L ≃ₐ[ℚ] L) :=
  (IsCyclotomicExtension.autEquivPow L (cyclotomic.irreducible_rat (NeZero.pos n))).symm

/-- The Artin map is normalised so that the class of `a` acts on `n`-th roots of unity
by `ζ ↦ ζ ^ a`. -/
