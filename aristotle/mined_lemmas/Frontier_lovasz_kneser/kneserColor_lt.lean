import Mathlib

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

/-!
# The Kneser graph and Lovász' theorem

The Kneser graph `KG_{n,k}` has as vertices the `k`-element subsets of an `n`-element set,
two of them being adjacent when they are disjoint.  Lovász' theorem (Kneser's conjecture)
states that its chromatic number equals `n - 2k + 2` for `n ≥ 2k`.

The upper bound `χ(KG_{n,k}) ≤ n - 2k + 2` is elementary and is proved here in full
generality (`Frontier.kneserGraph_colorable`).

The matching lower bound is the hard half; the known proofs go through the Borsuk–Ulam
theorem (or its combinatorial cousin, Tucker's lemma), neither of which is available in
Mathlib.  Here we prove the lower bound in the base cases that are accessible by the
Erdős–Ko–Rado theorem, namely `k = 1` (where `KG_{n,1}` is the complete graph `K_n`),
`n = 2k` (a perfect matching) and `n = 2k+1` (the odd graphs, e.g. the Petersen graph
`KG_{5,2}`).  This is the content of `Frontier.lovasz_kneser`.
-/

namespace Frontier

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`, and two
distinct such subsets are adjacent when they are disjoint. -/

lemma kneserColor_lt {n k : ℕ} (A : Finset (Fin n)) :
    kneserColor n k A < n - 2 * k + 2 := by
  unfold kneserColor
  split <;> omega

/-- Two disjoint `k`-sets receive different colours. -/
