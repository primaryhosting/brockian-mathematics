import Mathlib
namespace Brockian.MsPrimitiveRootCount
/-- The number of primitive roots modulo a prime p equals φ(p−1) (the number of generators of
    the cyclic group (ℤ/p)ˣ). -/
theorem primitive_root_count {p : ℕ} [Fact p.Prime] :
    (Finset.univ.filter (fun g : (ZMod p)ˣ => orderOf g = Fintype.card (ZMod p)ˣ)).card
      = Nat.totient (p - 1) := by
  sorry
end Brockian.MsPrimitiveRootCount
