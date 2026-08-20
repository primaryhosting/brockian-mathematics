/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph whose vertices carry a linear order:
the sum of the graph distances over all unordered pairs of distinct vertices
(each pair `{u, v}` counted once, via `u < v`). -/

noncomputable def wienerIndex {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) : ℕ :=
  ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 < p.2), G.dist p.1 p.2

/-- Along any walk in the path graph, the difference of the endpoint indices is at most
the length of the walk. -/
