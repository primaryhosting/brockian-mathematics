import Mathlib
namespace Brockian.GraphAcyclic

/-- Twin-admissible residue: both a and a+2 are units mod n. -/

lemma three_mul_inv (h3 : Nat.Coprime 3 M) : (3 : ZMod M) * (3 : ZMod M)⁻¹ = 1 := by
  simpa using ZMod.coe_mul_inv_eq_one (n := M) 3 h3

/-- Taking `ZMod.val` turns `+1` into `+1` on the integers, as long as we do not wrap to `0`. -/
