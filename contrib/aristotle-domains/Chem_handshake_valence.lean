/-!
# Handshake Valence
Category: Chemistry
Target: Chem.handshake_valence
Statement: Sum of atomic valences (vertex degrees) equals twice the number of bonds.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

variable {V : Type*} [DecidableEq V]

/-- The number of ends of the bond `e` that are attached to the atom `a`. -/
def bondIncidence (a : V) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun x y => (if x = a then 1 else 0) + (if y = a then 1 else 0),
    fun x y => by ring⟩

@[simp]
theorem bondIncidence_mk (a x y : V) :
    bondIncidence a s(x, y) = (if x = a then 1 else 0) + (if y = a then 1 else 0) := rfl

/-- The valence of an atom `a` in a molecule with bond multiset `bonds`: the total number of
bond-ends attached to `a`. -/
def valence (bonds : Multiset (Sym2 V)) (a : V) : ℕ :=
  (bonds.map (bondIncidence a)).sum

/-- Every bond has exactly two ends. -/
theorem sum_bondIncidence [Fintype V] (e : Sym2 V) : ∑ a : V, bondIncidence a e = 2 := by
  induction e with
  | _ x y => simp [Finset.sum_add_distrib]

/-- **Handshake lemma (chemistry form).** The sum of the atomic valences equals twice the
number of bonds. -/
theorem handshake_valence [Fintype V] (bonds : Multiset (Sym2 V)) :
    ∑ a : V, valence bonds a = 2 * Multiset.card bonds := by
  induction bonds using Multiset.induction_on with
  | empty => simp [valence]
  | cons e s ih =>
      simp only [valence] at ih ⊢
      simp only [Multiset.map_cons, Multiset.sum_cons, Finset.sum_add_distrib,
        Multiset.card_cons]
      rw [sum_bondIncidence e, ih]
      ring

end Chem

namespace Chem

/-- The same statement for a simple graph: the sum of the degrees (valences) of the vertices
is twice the number of edges. -/
theorem handshake_valence_simpleGraph {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ∑ a : V, G.degree a = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges

end Chem


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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

