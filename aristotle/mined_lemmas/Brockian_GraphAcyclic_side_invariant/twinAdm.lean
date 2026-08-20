import Mathlib
namespace Brockian.GraphAcyclic

/-- Twin-admissible residue: both a and a+2 are units mod n. -/

def twinAdm {n : ℕ} (a : ZMod n) : Prop := IsUnit a ∧ IsUnit (a + 2)

/-- The +3 flow graph on ℤ/n: a ~ b when they differ by ±3. -/
