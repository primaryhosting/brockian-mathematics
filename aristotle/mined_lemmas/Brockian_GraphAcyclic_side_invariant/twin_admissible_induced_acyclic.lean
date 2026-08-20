import Mathlib
namespace Brockian.GraphAcyclic

/-- Twin-admissible residue: both a and a+2 are units mod n. -/

theorem twin_admissible_induced_acyclic (M : ℕ) [NeZero M]
    (h3 : Nat.Coprime 3 M) (hM : 1 < M) :
    (SimpleGraph.induce {a : ZMod M | twinAdm a} (plusThreeGraph M)).IsAcyclic :=
  acyclic_of_int_height (height M) (height_injective h3) (height_step h3 hM)

end Brockian.GraphAcyclic

