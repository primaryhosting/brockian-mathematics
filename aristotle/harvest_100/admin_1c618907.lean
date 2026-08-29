import Mathlib

/-!
# Handshake Valence
Category: Chemistry
Target: Chem.handshake_valence
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of times an atom `v` occurs as an endpoint of an (unordered) bond `e`.
A self-bond `s(v, v)` contributes `2`. -/
def endpointCount (v : V) (e : Sym2 V) : ℕ :=
  Sym2.lift ⟨fun a b => (if a = v then 1 else 0) + (if b = v then 1 else 0),
    by intro a b; ring⟩ e

omit [Fintype V] in
@[simp]
theorem endpointCount_mk (v a b : V) :
    endpointCount v s(a, b) = (if a = v then 1 else 0) + (if b = v then 1 else 0) := rfl

/-- The valence of an atom `v` in a molecule whose bonds are given by the multiset `bonds`
(so that double and triple bonds are recorded with multiplicity): the number of bond
endpoints incident to `v`. -/
def valence (bonds : Multiset (Sym2 V)) (v : V) : ℕ :=
  (bonds.map (endpointCount v)).sum

/-- Every bond has exactly two endpoints, counted over all atoms. -/
theorem sum_endpointCount (e : Sym2 V) : ∑ v : V, endpointCount v e = 2 := by
  induction e with
  | _ a b =>
    simp only [endpointCount_mk, Finset.sum_add_distrib]
    simp

/-- **Handshake lemma for valences.** In any molecule, the sum of the valences of all atoms
equals twice the number of bonds. -/
theorem handshake_valence (bonds : Multiset (Sym2 V)) :
    ∑ v : V, valence bonds v = 2 * Multiset.card bonds := by
  induction bonds using Multiset.induction with
  | empty => simp [valence]
  | cons e s ih =>
    simp only [valence, Multiset.map_cons, Multiset.sum_cons] at *
    rw [Finset.sum_add_distrib, ih, sum_endpointCount, Multiset.card_cons]
    ring

omit [DecidableEq V] in
/-- Specialization to a simple molecular graph (single bonds only): the sum of the atomic
valences (vertex degrees) is twice the number of bonds (edges). -/
theorem handshake_valence_simpleGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges

#print axioms handshake_valence

end Chem

