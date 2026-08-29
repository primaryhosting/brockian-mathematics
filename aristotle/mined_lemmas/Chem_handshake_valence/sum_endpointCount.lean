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

theorem sum_endpointCount (e : Sym2 V) : ∑ v : V, endpointCount v e = 2 := by
  induction e with
  | _ a b =>
    simp only [endpointCount_mk, Finset.sum_add_distrib]
    simp

/-- **Handshake lemma for valences.** In any molecule, the sum of the valences of all atoms
equals twice the number of bonds. -/
