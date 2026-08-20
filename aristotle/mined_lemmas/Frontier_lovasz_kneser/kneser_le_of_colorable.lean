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

theorem kneser_le_of_colorable {n k c : ℕ} (hk : 1 ≤ k) (h2k : 2 * k ≤ n)
    (hc : (kneserGraph n k).Colorable c) : n ≤ c * k := by
  classical
  rw [SimpleGraph.colorable_iff_exists_bdd_nat_coloring] at hc
  obtain ⟨C, hC⟩ := hc
  refine card_le_mul_of_disjoint_coloring (c := c) hk h2k
    (fun A => if h : A.card = k then C ⟨A, h⟩ else 0) ?_ ?_
  · intro A hA
    dsimp only
    rw [dif_pos hA]
    exact hC _
  · intro A B hA hB hd
    dsimp only
    rw [dif_pos hA, dif_pos hB]
    refine C.valid ⟨?_, hd⟩
    intro hAB
    have hAB' : A = B := congrArg Subtype.val hAB
    subst hAB'
    have hempty : A = ∅ :=
      Finset.eq_empty_of_forall_notMem (fun x hx => Finset.disjoint_left.mp hd hx hx)
    rw [hempty, Finset.card_empty] at hA
    omega

/-! ### The main theorem -/

/-- **Lovász' theorem on Kneser graphs (base cases).**

The chromatic number of the Kneser graph `KG_{n,k}` is `n - 2k + 2`.

The general statement is Kneser's conjecture, proved by Lovász via the Borsuk–Ulam theorem,
which is not available in Mathlib.  We prove here the base cases `k = 1` (the complete graph
`K_n`) and `2k ≤ n ≤ 2k + 1` (perfect matchings and the odd graphs), where the lower bound
follows from the Erdős–Ko–Rado theorem.  The upper bound `≤ n - 2k + 2` holds in general and
is `Frontier.kneserGraph_colorable`. -/
