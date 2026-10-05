import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## The Boolean cube as an `𝔽₂`-vector space -/

/-- `n`-bit strings, viewed as the elementary abelian 2-group `(ℤ/2)ⁿ`;
addition is bitwise XOR. -/
abbrev V (n : ℕ) : Type := Fin n → ZMod 2


lemma exists_solving_tree :
    Solves (DTree.query (n := 1) (d := 1) (0 : V 1)
      (fun a => DTree.query (d := 0) (1 : V 1) (fun b => DTree.leaf (decide (a = b))))) := by
  have h01 : (0 : V 1) ≠ 1 := by
    intro h
    have h0 := congrFun h 0
    simp only [Pi.zero_apply, Pi.one_apply] at h0
    exact absurd h0 (by decide)
  constructor
  · intro f hf
    simp only [DTree.run, decide_eq_false_iff_not]
    intro hcon
    exact h01 (hf hcon)
  · intro f s hs hshift
    have hs1 : s = 1 := by
      have h : s 0 ≠ 0 := by
        intro h0
        exact hs (funext fun i => by rw [Subsingleton.elim i 0]; exact h0)
      have h1 : s 0 = 1 := zmod2_eq_one_of_ne_zero h
      funext i
      rw [Subsingleton.elim i 0, Pi.one_apply]
      exact h1
    have hfeq : f 0 = f 1 := by
      refine (hshift 0 1).mpr (Or.inr ?_)
      rw [zero_add, hs1]
    simp only [DTree.run, decide_eq_true_iff]
    exact hfeq

/-! ## Main statement -/

/-- **Simon's problem.**

* (1) and (2): the quantum algorithm.  The measurement outcomes of Simon's circuit are
  *uniformly distributed on the hyperplane* `s^⊥` orthogonal to the hidden shift `s`:
  outcomes off that hyperplane have amplitude `0`, and each of the outcomes on it has
  probability `2 / 2ⁿ`.
* (3): `O(n)` such outcomes determine `s` — there is a set of at most `n` vectors whose
  joint orthogonal complement is exactly `{0, s}`.  So `O(n)` quantum queries suffice.
* (4): classically, every deterministic query algorithm solving Simon's problem (deciding
  whether the oracle is one-to-one or two-to-one with a nonzero hidden shift) needs at
  least `2^(n/2)` queries: `Ω(2^{n/2})`. -/
