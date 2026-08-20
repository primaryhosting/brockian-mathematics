/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset SimpleGraph

namespace Chem

/-- The Wiener index of a finite graph: the sum of the graph distances over all
unordered pairs of distinct vertices (indexed here by ordered pairs `i < j`). -/

noncomputable def wiener {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) : ℕ :=
  ∑ i : V, ∑ j ∈ Finset.univ.filter (fun j => i < j), G.dist i j

/-- Any walk in the path graph is at least as long as the numeric distance of its endpoints. -/
