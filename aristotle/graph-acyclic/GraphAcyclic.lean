import Mathlib
namespace Brockian.GraphAcyclic

/-- Twin-admissible residue: both a and a+2 are units mod n. -/
def twinAdm {n : ℕ} (a : ZMod n) : Prop := IsUnit a ∧ IsUnit (a + 2)

/-- The +3 flow graph on ℤ/n: a ~ b when they differ by ±3. -/
def plusThreeGraph (n : ℕ) : SimpleGraph (ZMod n) where
  Adj a b := (b - a = 3 ∨ a - b = 3) ∧ a ≠ b
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

/-- Gate sub-brick 2 (the hard SimpleGraph step): for a modulus M coprime to 3, the induced
subgraph of the +3 flow on the twin-admissible residues is ACYCLIC. Intuition: when gcd(3,M)=1
the +3 map is a single M-cycle over all of ℤ/M; the residue 0 is never twin-admissible (0 is not
a unit for M>1), so the admissible vertex set is a PROPER subset — deleting ≥1 vertex from a cycle
leaves a disjoint union of paths, which has no cycle. (Arithmetic facts available to reproduce:
`a + 3*(k:ZMod M) = a → M ∣ k` for a unit 3, and 0 is not a unit in a nontrivial ZMod M.) -/
theorem twin_admissible_induced_acyclic (M : ℕ) [NeZero M]
    (h3 : Nat.Coprime 3 M) (hM : 1 < M) :
    (SimpleGraph.induce {a : ZMod M | twinAdm a} (plusThreeGraph M)).IsAcyclic := by
  sorry

end Brockian.GraphAcyclic
