import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

namespace Frontier

section

variable {V : Type*} [Fintype V]

/-- The bilinear form `xᵀ A y` associated to a weight matrix `A`. -/

lemma bil_cind {A : V → V → ℝ} {d : ℝ} (hsymm : ∀ i j, A i j = A j i)
    (hreg : ∀ i, ∑ j, A i j = d) (hn : (Fintype.card V : ℝ) ≠ 0) (S T : Finset V) :
    bil A (cind S) (cind T)
      = (∑ i ∈ S, ∑ j ∈ T, A i j) - d * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) := by
  have hcol : ∀ j, ∑ i, A i j = d := by
    intro j
    rw [show ∑ i, A i j = ∑ i, A j i from Finset.sum_congr rfl fun i _ => hsymm i j]
    exact hreg j
  have expand : bil A (cind S) (cind T)
      = bil A (indf S) (indf T)
        - ((T.card : ℝ) / (Fintype.card V : ℝ)) * bil A (indf S) onev
        - (((S.card : ℝ) / (Fintype.card V : ℝ)) * bil A onev (indf T)
          - ((S.card : ℝ) / (Fintype.card V : ℝ))
            * (((T.card : ℝ) / (Fintype.card V : ℝ)) * bil A onev onev)) := by
    have hc : ∀ U : Finset V,
        cind U = fun i => indf U i - ((U.card : ℝ) / (Fintype.card V : ℝ)) * onev i :=
      fun U => rfl
    rw [hc S, hc T, bil_sub_left, bil_sub_right, bil_sub_right, bil_smul_left, bil_smul_right,
      bil_smul_right, bil_smul_left]
    ring
  rw [expand, bil_ind_ind, bil_ind_one hreg, bil_one_ind hcol, bil_one_one hreg]
  field_simp
  ring

end

/-- **Expander mixing lemma** (Alon–Chung / Wigderson form).

Let `A` be a symmetric real weight matrix on a finite vertex set `V` which is `d`-regular
(all row sums equal `d`), and suppose that the Rayleigh quotient of `A` is bounded in absolute
value by `lam ≥ 0` on the space of vectors orthogonal to the all-ones vector (i.e. `lam` bounds
the second eigenvalue of `A` in absolute value).  Then for all sets of vertices `S`, `T`, the
number of edges between `S` and `T` deviates from its "expected" value `d |S| |T| / |V|` by at
most `lam * sqrt (|S| |T|)`. -/
