import Mathlib
namespace Brockian.GraphAcyclic

/-- Twin-admissible residue: both a and a+2 are units mod n. -/

noncomputable def height (M : ℕ) (v : {a : ZMod M | twinAdm a}) : ℤ :=
  (((v : ZMod M) * (3 : ZMod M)⁻¹).val : ℤ)

