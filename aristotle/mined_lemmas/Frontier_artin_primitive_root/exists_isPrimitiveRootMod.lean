import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root modulo `p`* when its residue generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/

lemma exists_isPrimitiveRootMod {p : ℕ} (hp : p.Prime) :
    ∃ a : ℤ, IsPrimitiveRootMod a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  refine ⟨((g : ZMod p).val : ℤ), ?_⟩
  have hcast : ((((g : ZMod p).val : ℤ)) : ZMod p) = ((g : ZMod p)) := by
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  rw [IsPrimitiveRootMod, hcast, orderOf_units,
    orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient,
    Nat.totient_prime hp]

/-- There are infinitely many primes possessing a primitive root (unconditionally). -/
