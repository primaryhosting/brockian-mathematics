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

theorem artinMap_apply_root_of_unity (a : (ZMod n)ˣ) (x : L) (hx : x ^ n = 1) :
    artinMap n L a x = x ^ ((a : ZMod n).val) := by
  have h : Irreducible (cyclotomic n ℚ) := cyclotomic.irreducible_rat (NeZero.pos n)
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ L) n :=
    IsCyclotomicExtension.zeta_spec n ℚ L
  have hpow : hζ.autToPow ℚ (artinMap n L a) = a := by
    have := (IsCyclotomicExtension.autEquivPow (n := n) (K := ℚ) L h).apply_symm_apply a
    simpa [artinMap, IsCyclotomicExtension.autEquivPow_apply] using this
  have hζ' : artinMap n L a (IsCyclotomicExtension.zeta n ℚ L)
      = (IsCyclotomicExtension.zeta n ℚ L) ^ ((a : ZMod n).val) := by
    have key := hζ.autToPow_spec ℚ (artinMap n L a)
    rw [hpow] at key
    exact key.symm
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, hζ', ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- An automorphism of a cyclotomic extension is determined by its effect on
the `n`-th roots of unity. -/
