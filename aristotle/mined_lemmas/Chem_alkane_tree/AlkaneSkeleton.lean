import Mathlib

/-!
# Alkane Tree
Category: Chemistry
Target: Chem.alkane_tree
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Chem

/-- The carbon skeleton of an acyclic alkane with `n` carbon atoms: a simple graph on the
`n` carbons which is connected (the molecule is one piece), acyclic (the alkane is acyclic,
i.e. not a cycloalkane) and in which every carbon has at most `4` bonds (carbon is
tetravalent). -/
structure AlkaneSkeleton (n : ℕ) where
  /-- The graph of carbon–carbon bonds. -/
  G : SimpleGraph (Fin n)
  /-- The skeleton is connected. -/
  connected : G.Connected
  /-- The skeleton is acyclic. -/
  acyclic : G.IsAcyclic
  /-- Carbon is tetravalent: at most four bonds at each carbon. -/
  valence : ∀ v, G.degree v ≤ 4

variable {n : ℕ}

/-- The number of C–C bonds in the skeleton. -/

theorem AlkaneSkeleton.isTree (A : AlkaneSkeleton n) : A.G.IsTree :=
  ⟨A.connected, A.acyclic⟩

/-- **Alkane tree theorem.**  The carbon skeleton of an acyclic alkane on `n` carbons is a
tree, it has exactly `n - 1` carbon–carbon bonds, and consequently the molecule carries
`2n + 2` hydrogen atoms, i.e. it has formula `CₙH₂ₙ₊₂`. -/
