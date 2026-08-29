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
