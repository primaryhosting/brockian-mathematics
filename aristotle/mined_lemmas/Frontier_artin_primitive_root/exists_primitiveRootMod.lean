import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` when its residue class generates the
multiplicative group of `ZMod p`, i.e. when it has multiplicative order `p - 1`. -/

lemma exists_primitiveRootMod (p : ℕ) (hp : p.Prime) : ∃ a : ℤ, IsPrimitiveRootMod a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  refine ⟨((g : ZMod p).val : ℤ), ?_⟩
  have hcast : ((((g : ZMod p).val : ℤ)) : ZMod p) = ((g : ZMod p)) := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rfl
  rw [IsPrimitiveRootMod, hcast, orderOf_units,
    orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime hp]

/-- For a perfect square `a`, the set of primes having `a` as a primitive root is contained
in `{2}`, hence finite: Artin's conjecture genuinely fails for such `a`. -/
