import Mathlib
/-!
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
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

namespace CS

/-!
## Constraint graphs (binary CSPs)

Dinur's proof of the PCP theorem is phrased in terms of *constraint graphs*: binary
constraint satisfaction problems whose variables are the vertices of a graph and whose
constraints sit on the edges.  We model such an instance by

* a number `n` of variables, indexed by `Fin n`;
* an alphabet `Fin q` with `q > 0`;
* a list `cs` of constraints, each a triple `(u, v, R)` with `u v : Fin n` and
  `R : Fin q → Fin q → Bool`.

An assignment is a map `Fin n → Fin q`, and the *unsat value* `UNSAT G` is the minimum,
over all assignments, of the fraction of constraints that are violated.
-/

/-- A binary constraint satisfaction instance ("constraint graph"): `n` variables taking
values in an alphabet of size `q > 0`, subject to a list of binary constraints. -/
structure ConstraintGraph where
  /-- Number of variables. -/
  n : ℕ
  /-- Size of the alphabet. -/
  q : ℕ
  /-- The alphabet is nonempty. -/
  hq : 0 < q
  /-- The list of constraints, each relating two variables. -/
  cs : List (Fin n × Fin n × (Fin q → Fin q → Bool))

namespace ConstraintGraph

variable (G : ConstraintGraph)

/-- The "all-zero" assignment; it exists because the alphabet is nonempty. -/

lemma UNSAT_iterate_ge (hα : 0 ≤ α)
    (hgap : ∀ G, min (2 * UNSAT G) α ≤ UNSAT (amp G))
    (k : ℕ) (G : ConstraintGraph) :
    min (2 ^ k * UNSAT G) α ≤ UNSAT (amp^[k] G) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine le_trans ?_ (hgap (amp^[k] G))
      have hpow : (2 : ℚ) ^ (k + 1) * UNSAT G = 2 * (2 ^ k * UNSAT G) := by ring
      rw [le_min_iff]
      refine ⟨?_, min_le_right _ _⟩
      rcases le_total ((2 : ℚ) ^ k * UNSAT G) α with h | h
      · rw [min_eq_left h] at ih
        have h1 : min ((2 : ℚ) ^ (k + 1) * UNSAT G) α ≤ 2 ^ (k + 1) * UNSAT G :=
          min_le_left _ _
        linarith
      · rw [min_eq_right h] at ih
        have h1 : min ((2 : ℚ) ^ (k + 1) * UNSAT G) α ≤ α := min_le_right _ _
        linarith

end Amplification

/-!
## The PCP theorem via gap amplification
-/

/--
**Dinur's gap-amplification proof of the PCP theorem.**

Assume Dinur's *Main Lemma*: there are a constant alphabet size `q₀`, a size-blow-up
constant `C`, a gap constant `α > 0`, and a transformation `amp` of binary constraint
graphs such that for every instance `G`:

* `amp G` uses the fixed alphabet `Fin q₀`;
* `size (amp G) ≤ C * size G` (linear size blow-up);
* `amp G` is satisfiable whenever `G` is (perfect completeness);
* `UNSAT (amp G) ≥ min (2 * UNSAT G, α)` (gap amplification).

Then, for every constraint graph `G` and every `k` with `α * size G ≤ 2 ^ k` — i.e. for
`k` logarithmic in the size of `G` — one obtains an instance `G'` over the fixed alphabet
`Fin q₀` of size at most `C ^ (k+1) * size G` (polynomial in `size G`, since `k` is
logarithmic) which is satisfiable if `G` is, and whose unsat value is at least the
constant `α` whenever `G` is unsatisfiable.

This is exactly the gap-CSP form of the PCP theorem: deciding satisfiability of `G`
reduces to distinguishing `UNSAT G' = 0` from `UNSAT G' ≥ α`, a constant gap.
-/
