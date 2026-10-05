import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace CS

/-! ## A recursive description of the permanent

`pm M l C` is the weighted count of bijections from the rows listed in `l` onto the
column set `C`, where the weight of a bijection is the product of the corresponding
matrix entries.  It is a convenient recursive handle on the permanent. -/

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommSemiring R]

/-- Weighted count of the bijections from the rows in the list `l` onto the columns in `C`. -/

theorem pm_eq_permanent (M : Matrix ι ι R) :
    pm (fun i j => M i j) Finset.univ.toList Finset.univ = M.permanent := by
  rw [pm_eq_sum_bijs _ _ (Finset.nodup_toList _) _ (by simp), sum_bijs_univ,
    permanent_eq_sum_perm]

/-! ## The permanent of a 0/1 matrix is a counting function

For a matrix with entries in `{0,1}`, the permanent is literally the number of
permutations `σ` all of whose entries `M i (σ i)` are `1`, i.e. the number of perfect
matchings of the associated bipartite graph.  Membership of the 0/1 permanent in `#P`
is exactly this statement: it counts the witnesses of a relation that can be checked in
polynomial time (here: check `n` matrix entries). -/

