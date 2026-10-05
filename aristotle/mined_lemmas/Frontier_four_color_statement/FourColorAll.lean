import Mathlib

/-!
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
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

namespace Frontier

open SimpleGraph

/-! ## Minors and planarity -/

/-- `IsMinor H G` says that `H` is a *minor* of `G`: there is a family of pairwise disjoint
"branch sets" `B w ⊆ V`, one for each vertex `w` of `H`, each inducing a connected subgraph
of `G`, such that adjacent vertices of `H` have branch sets joined by an edge of `G`. -/

def FourColorAll : Prop :=
  ∀ (V : Type) (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-- **Four Color Statement (Lean-checked reduction to the finite case).**
Every planar graph — of arbitrary cardinality — is 4-colourable **if and only if** every *finite*
planar graph is 4-colourable.  The substantive direction is a compactness argument
(De Bruijn–Erdős) combined with the fact that planarity, in Wagner's minor-free form, is
inherited by induced subgraphs.  The finite case itself is the Appel–Haken theorem, which is
taken here as the hypothesis `FourColorFinite`. -/
