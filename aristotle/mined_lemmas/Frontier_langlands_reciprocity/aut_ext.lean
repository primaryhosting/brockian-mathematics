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

theorem aut_ext {σ τ : L ≃ₐ[ℚ] L}
    (h : ∀ x : L, x ^ n = 1 → σ x = τ x) : σ = τ := by
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ L) n :=
    IsCyclotomicExtension.zeta_spec n ℚ L
  apply AlgEquiv.coe_algHom_injective
  apply (hζ.powerBasis ℚ).algHom_ext
  simpa [hζ.powerBasis_gen ℚ] using h _ hζ.pow_eq_one

/-- The Frobenius at a prime `p` unramified in `ℚ(ζ_n)/ℚ` (i.e. `p ∤ n`) is the image
under the Artin map of the class of `p`. -/
