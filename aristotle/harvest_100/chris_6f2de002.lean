/-
# Handshake Valence
Category: Chemistry
Target: Chem.handshake_valence
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- below as the module docstring.)
import Mathlib

/-!
# Handshake Valence
Category: Chemistry
Target: Chem.handshake_valence
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

/-- A molecule: a finite set of atoms `V` together with a list of bonds, each bond being an
ordered pair of atoms (the list allows multiple bonds between the same pair of atoms, as in
double and triple bonds). -/
structure Molecule (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The bonds of the molecule, listed with multiplicity. -/
  bonds : List (V × V)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The valence of an atom: the number of bond endpoints attached to it.  A double bond
contributes `2`, and a (hypothetical) self-bond contributes `2` as well. -/
def Molecule.valence (M : Molecule V) (v : V) : ℕ :=
  (M.bonds.countP fun b => b.1 = v) + (M.bonds.countP fun b => b.2 = v)

/-- Each bond has exactly one first endpoint, so summing over all atoms the number of bonds
whose first endpoint is that atom recovers the number of bonds. -/
lemma sum_countP_fst (l : List (V × V)) :
    (∑ v : V, l.countP fun b => b.1 = v) = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.countP_cons, List.length_cons, Finset.sum_add_distrib, ih]
      simp [Finset.sum_ite_eq]

/-- Each bond has exactly one second endpoint. -/
lemma sum_countP_snd (l : List (V × V)) :
    (∑ v : V, l.countP fun b => b.2 = v) = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.countP_cons, List.length_cons, Finset.sum_add_distrib, ih]
      simp [Finset.sum_ite_eq]

/-- **Handshake lemma for valences.**  The sum of the atomic valences of a molecule equals twice
the number of bonds. -/
theorem handshake_valence (M : Molecule V) :
    (∑ v : V, M.valence v) = 2 * M.bonds.length := by
  simp only [Molecule.valence, Finset.sum_add_distrib, sum_countP_fst, sum_countP_snd]
  ring

omit [DecidableEq V] in
/-- The same statement for a `SimpleGraph` model of a molecule (single bonds only):
the sum of the degrees is twice the number of bonds. -/
theorem handshake_valence_simpleGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, G.degree v) = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges

end Chem

