import Mathlib
namespace C4.BChar

/-- The dihedral group of order `2n` has exactly `2n` elements. -/

theorem cyclic_gen_zmod5 : ∃ g : (ZMod 5)ˣ, orderOf g = 4 := by
  refine ⟨ZMod.unitOfCoprime 2 (by decide), ?_⟩
  have h := orderOf_eq_prime_pow
    (x := ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 5)) (p := 2) (n := 1)
    (by decide) (by decide)
  simpa using h

end C4.BChar

