import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

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

/-- The state space of a single quantum system of (Hilbert space) dimension `4`. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- A *noncontextual hidden-variable assignment* (a Kochen–Specker colouring) is a map that
assigns to every unit vector (equivalently, to every rank-one orthogonal projection) a
definite truth value `0`/`1`, in such a way that for every orthonormal basis exactly one
basis vector receives the value `1`.

Note that in dimension `4` an orthonormal family indexed by `Fin 4` is automatically an
orthonormal *basis* (see `Frontier.orthonormal_four_spans`), so the quantification below is
exactly the quantification over all orthonormal bases. -/

theorem val_sum_eq_one {f : E4 → Bool} (hf : KSAssignment f) (a b c d : E4)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : ⟪a, b⟫ = 0) (hac : ⟪a, c⟫ = 0) (had : ⟪a, d⟫ = 0)
    (hbc : ⟪b, c⟫ = 0) (hbd : ⟪b, d⟫ = 0) (hcd : ⟪c, d⟫ = 0) :
    val f a + val f b + val f c + val f d = 1 := by
  have hv : Orthonormal ℝ
      (fun i => ‖(![a, b, c, d] : Fin 4 → E4) i‖⁻¹ • (![a, b, c, d] : Fin 4 → E4) i) := by
    refine orthonormal_normalize _ ?_ ?_
    · intro i; fin_cases i <;> assumption
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [real_inner_comm a b, real_inner_comm a c, real_inner_comm a d,
          real_inner_comm b c, real_inner_comm b d, real_inner_comm c d]
  obtain ⟨i, hi, hu⟩ := hf _ hv
  have ka : f (nrm a) = true → (0 : Fin 4) = i := hu 0
  have kb : f (nrm b) = true → (1 : Fin 4) = i := hu 1
  have kc : f (nrm c) = true → (2 : Fin 4) = i := hu 2
  have kd : f (nrm d) = true → (3 : Fin 4) = i := hu 3
  show (if f (nrm a) = true then 1 else 0) + (if f (nrm b) = true then 1 else 0)
      + (if f (nrm c) = true then 1 else 0) + (if f (nrm d) = true then 1 else 0) = 1
  fin_cases i
  · have hia : f (nrm a) = true := hi
    rw [if_pos hia, if_neg (fun h => by simpa using kb h), if_neg (fun h => by simpa using kc h),
      if_neg (fun h => by simpa using kd h)]
  · have hib : f (nrm b) = true := hi
    rw [if_neg (fun h => by simpa using ka h), if_pos hib, if_neg (fun h => by simpa using kc h),
      if_neg (fun h => by simpa using kd h)]
  · have hic : f (nrm c) = true := hi
    rw [if_neg (fun h => by simpa using ka h), if_neg (fun h => by simpa using kb h), if_pos hic,
      if_neg (fun h => by simpa using kd h)]
  · have hid : f (nrm d) = true := hi
    rw [if_neg (fun h => by simpa using ka h), if_neg (fun h => by simpa using kb h),
      if_neg (fun h => by simpa using kc h), if_pos hid]

/-- Coordinate version of `Frontier.val_sum_eq_one`: all hypotheses are purely numerical. -/
