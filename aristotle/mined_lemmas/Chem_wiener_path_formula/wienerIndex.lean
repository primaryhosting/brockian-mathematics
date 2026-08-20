/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
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

set_option grind.warning false

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices, i.e. half the sum of `dist u v` over all ordered pairs. -/

noncomputable def wienerIndex {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (∑ u : V, ∑ v : V, G.dist u v) / 2

/-- Any walk in the path graph is at least as long as the difference of the indices
of its endpoints. -/
