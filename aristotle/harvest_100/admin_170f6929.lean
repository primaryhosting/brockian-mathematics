/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Phys

/-- An explicit Kochen–Specker set of 18 vectors in `ℝ⁴` (all entries in `{0, 1, -1}`).
They are grouped by `ksBasis` into nine orthogonal bases, each vector belonging to
exactly two of the nine bases. -/
def ksVec : Fin 18 → (Fin 4 → ℝ) :=
  ![![0, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1],
    ![0, 1, 0, 1], ![0, 1, 1, 0], ![1, -1, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1],
    ![1, -1, 1, 1], ![1, 0, -1, 0], ![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 1, -1, -1],
    ![1, 1, 0, 0], ![1, 1, 1, -1], ![1, 1, 1, 1]]

/-- The nine orthogonal bases of the Kochen–Specker set, given as indices into `ksVec`.
Each of the 18 indices occurs in exactly two of these nine quadruples. -/
def ksBasis : Fin 9 → Fin 4 → Fin 18 :=
  ![![0, 2, 8, 15], ![0, 3, 6, 12], ![1, 7, 10, 15], ![1, 8, 14, 17], ![2, 4, 5, 12],
    ![3, 7, 13, 16], ![4, 9, 11, 17], ![5, 10, 11, 16], ![6, 9, 13, 14]]

/-- Every vector of the Kochen–Specker set is nonzero. -/
lemma ksVec_ne_zero (n : Fin 18) : ksVec n ≠ 0 := by
  intro h
  fin_cases n <;>
    · rw [funext_iff] at h
      revert h
      norm_num [ksVec, Fin.forall_fin_succ]

/-- Distinct vectors inside one of the nine listed quadruples are orthogonal. -/
lemma ksBasis_orth (i : Fin 9) (j k : Fin 4) (hjk : j ≠ k) :
    ∑ m, ksVec (ksBasis i j) m * ksVec (ksBasis i k) m = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [ksVec, ksBasis, Fin.sum_univ_four]

/-- **Kochen–Specker theorem via an explicit 18-vector set.**
There is no `{0,1}`-coloring `c` of the nonzero vectors of `ℝ⁴` assigning the value `1`
to exactly one vector of every orthogonal basis (i.e. with `c x + c y + c z + c w = 1`
for every four pairwise orthogonal nonzero vectors `x, y, z, w`).  The proof exhibits the
explicit 18-vector set `ksVec`, which forms nine orthogonal bases (`ksBasis`) in which each
vector occurs exactly twice: summing the nine basis equations gives `2 * N = 9`, which is
impossible.  (The hypothesis `hc01` that `c` takes only the values `0` and `1` is recorded
as part of the statement of a `{0,1}`-coloring; it is in fact implied by `hbasis` together
with `c` being `ℕ`-valued, so the proof does not need it.) -/
theorem kochen_specker_18
    (c : (Fin 4 → ℝ) → ℕ)
    (hc01 : ∀ x : Fin 4 → ℝ, c x = 0 ∨ c x = 1)
    (hbasis : ∀ x y z w : Fin 4 → ℝ, x ≠ 0 → y ≠ 0 → z ≠ 0 → w ≠ 0 →
      (∑ m, x m * y m) = 0 → (∑ m, x m * z m) = 0 → (∑ m, x m * w m) = 0 →
      (∑ m, y m * z m) = 0 → (∑ m, y m * w m) = 0 → (∑ m, z m * w m) = 0 →
      c x + c y + c z + c w = 1) :
    False := by
  have key : ∀ i : Fin 9,
      c (ksVec (ksBasis i 0)) + c (ksVec (ksBasis i 1)) + c (ksVec (ksBasis i 2)) +
        c (ksVec (ksBasis i 3)) = 1 := fun i =>
    hbasis _ _ _ _ (ksVec_ne_zero _) (ksVec_ne_zero _) (ksVec_ne_zero _) (ksVec_ne_zero _)
      (ksBasis_orth i 0 1 (by decide)) (ksBasis_orth i 0 2 (by decide))
      (ksBasis_orth i 0 3 (by decide)) (ksBasis_orth i 1 2 (by decide))
      (ksBasis_orth i 1 3 (by decide)) (ksBasis_orth i 2 3 (by decide))
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  have h3 := key 3
  have h4 := key 4
  have h5 := key 5
  have h6 := key 6
  have h7 := key 7
  have h8 := key 8
  simp only [ksBasis, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  omega

#print axioms Phys.kochen_specker_18

end Phys

