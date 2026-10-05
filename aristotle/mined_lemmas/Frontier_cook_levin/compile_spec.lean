import Mathlib
import RequestProject.Hardness

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Cook–Levin theorem

`SAT` is NP-complete:

* `SAT ∈ NP`, and
* every language in `NP` reduces to `SAT`.

Here languages are sets of bit strings; a language is in `NP` when it is decided by a
family of polynomial size Boolean circuits reading the input word together with a
witness word of polynomial length (`Frontier.InNP`).  `SAT` is the set of bit strings
whose associated CNF formula is satisfiable (`Frontier.SATlang`), the association being
the occurrence-matrix encoding of `Frontier.decodeCNF`.

The reductions produced here are *projections*: each output bit is a constant, or a bit
of the input word, or the negation of a bit of the input word, and the number of output
bits is polynomial in the length of the input word (`Frontier.IsProjectionReduction`).
In particular they are computable by polynomial size circuits.

The circuit families witnessing membership in `NP` are not required to be uniformly
generated, so `Frontier.InNP` is the non-uniform version of `NP`; correspondingly the
reductions produced by the hardness proof are non-uniform (but they are projections,
which is a much more restrictive class than polynomial time computable maps).
-/

namespace Frontier

/-- `L₁` reduces to `L₂` by a projection reduction. -/

theorem compile_spec (x : ℕ → Bool) (t : Tree) (base : ℕ) (pre : Circ) (h : pre.length = base) :
    (vals x (pre ++ t.compile base)).getD (base + t.size - 1) false = t.eval x := by
  induction t generalizing base pre with
  | var i =>
      have : base + size (Tree.var i) - 1 = pre.length := by simp [size, h]
      rw [this]
      simpa [compile, Gate.eval, eval] using vals_getD_concat x pre (Gate.inp i)
  | lit b =>
      have : base + size (Tree.lit b) - 1 = pre.length := by simp [size, h]
      rw [this]
      simpa [compile, Gate.eval, eval] using vals_getD_concat x pre (Gate.const b)
  | neg t ih =>
      have happ : pre ++ (Tree.neg t).compile base
          = (pre ++ t.compile base) ++ [Gate.neg (base + t.size - 1)] := by
        simp [compile, List.append_assoc]
      have hlen : (pre ++ t.compile base).length = base + t.size := by simp [h]
      have hidx : base + (Tree.neg t).size - 1 = (pre ++ t.compile base).length := by
        have := t.size_pos; simp [size, hlen]
      rw [happ, hidx, vals_getD_concat]
      simp only [Gate.eval, eval]
      rw [ih base pre h]
  | conj t u iht ihu =>
      have happ : pre ++ (Tree.conj t u).compile base
          = ((pre ++ t.compile base) ++ u.compile (base + t.size)) ++
              [Gate.conj (base + t.size - 1) (base + t.size + u.size - 1)] := by
        simp [compile, List.append_assoc]
      have hlen1 : (pre ++ t.compile base).length = base + t.size := by simp [h]
      have hlen2 : ((pre ++ t.compile base) ++ u.compile (base + t.size)).length
          = base + t.size + u.size := by simp [h]; omega
      have hidx : base + (Tree.conj t u).size - 1
          = ((pre ++ t.compile base) ++ u.compile (base + t.size)).length := by
        have h1 := t.size_pos
        have h2 := u.size_pos
        rw [hlen2]
        simp only [size]
        omega
      rw [happ, hidx, vals_getD_concat]
      simp only [Gate.eval, eval]
      have h1 : (vals x ((pre ++ t.compile base) ++ u.compile (base + t.size))).getD
          (base + t.size - 1) false = t.eval x := by
        rw [vals_getD_append x _ _ (by rw [hlen1]; have := t.size_pos; omega)]
        exact iht base pre h
      have h2 : (vals x ((pre ++ t.compile base) ++ u.compile (base + t.size))).getD
          (base + t.size + u.size - 1) false = u.eval x := by
        have := ihu (base + t.size) (pre ++ t.compile base) hlen1
        rw [show base + t.size + u.size - 1 = base + t.size + u.size - 1 from rfl]
        simpa using this
      rw [h1, h2]
  | disj t u iht ihu =>
      have happ : pre ++ (Tree.disj t u).compile base
          = ((pre ++ t.compile base) ++ u.compile (base + t.size)) ++
              [Gate.disj (base + t.size - 1) (base + t.size + u.size - 1)] := by
        simp [compile, List.append_assoc]
      have hlen1 : (pre ++ t.compile base).length = base + t.size := by simp [h]
      have hlen2 : ((pre ++ t.compile base) ++ u.compile (base + t.size)).length
          = base + t.size + u.size := by simp [h]; omega
      have hidx : base + (Tree.disj t u).size - 1
          = ((pre ++ t.compile base) ++ u.compile (base + t.size)).length := by
        have h1 := t.size_pos
        have h2 := u.size_pos
        rw [hlen2]
        simp only [size]
        omega
      rw [happ, hidx, vals_getD_concat]
      simp only [Gate.eval, eval]
      have h1 : (vals x ((pre ++ t.compile base) ++ u.compile (base + t.size))).getD
          (base + t.size - 1) false = t.eval x := by
        rw [vals_getD_append x _ _ (by rw [hlen1]; have := t.size_pos; omega)]
        exact iht base pre h
      have h2 : (vals x ((pre ++ t.compile base) ++ u.compile (base + t.size))).getD
          (base + t.size + u.size - 1) false = u.eval x := by
        have := ihu (base + t.size) (pre ++ t.compile base) hlen1
        simpa using this
      rw [h1, h2]

/-- The compiled circuit of a formula computes the value of the formula. -/
