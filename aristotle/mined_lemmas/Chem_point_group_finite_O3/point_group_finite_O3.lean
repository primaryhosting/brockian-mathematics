import Mathlib

/-!
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix

/-- The **point group** of a molecule whose nuclei occupy the positions `S ⊆ ℝ³`:
the subgroup of the orthogonal group `O(3)` consisting of those orthogonal
transformations that map the set of nuclear positions onto itself. -/

theorem point_group_finite_O3 (S : Set (Fin 3 → ℝ)) (hfin : S.Finite)
    (hspan : Submodule.span ℝ S = ⊤) : Finite (pointGroup S) := by
  haveI : Finite S := hfin.to_subtype
  -- Restriction to `S` gives an injection of the point group into the self-maps of `S`.
  have hmem : ∀ (A : pointGroup S) (s : S),
      ((A : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).mulVec (s : Fin 3 → ℝ)
        ∈ S := by
    intro A s
    have hA : (fun v => ((A : Matrix.orthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ).mulVec v) '' S = S := A.2
    have hs : ((A : Matrix.orthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ).mulVec (s : Fin 3 → ℝ)
        ∈ (fun v => ((A : Matrix.orthogonalGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ).mulVec v) '' S := ⟨s, s.2, rfl⟩
    rwa [hA] at hs
  refine Finite.of_injective (fun A => fun s : S => (⟨_, hmem A s⟩ : S)) ?_
  intro A B hAB
  have hEq : ∀ v ∈ S,
      ((A : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).mulVec v
        = ((B : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).mulVec v := by
    intro v hv
    have := congrFun hAB ⟨v, hv⟩
    exact congrArg Subtype.val this
  have hlin : Matrix.toLin' ((A : Matrix.orthogonalGroup (Fin 3) ℝ) :
      Matrix (Fin 3) (Fin 3) ℝ) = Matrix.toLin' ((B : Matrix.orthogonalGroup (Fin 3) ℝ) :
      Matrix (Fin 3) (Fin 3) ℝ) := by
    refine LinearMap.ext_on hspan ?_
    intro v hv
    simpa [Matrix.toLin'_apply] using hEq v hv
  have : ((A : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
      = ((B : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) :=
    Matrix.toLin'.injective hlin
  exact Subtype.ext (Subtype.ext this)

/-- Non-vacuity check: the hypotheses of `point_group_finite_O3` are satisfiable, e.g. by the
three unit vectors along the coordinate axes. -/
example : ∃ S : Set (Fin 3 → ℝ), S.Finite ∧ Submodule.span ℝ S = ⊤ := by
  refine ⟨Set.range (fun i : Fin 3 => (Pi.single i (1 : ℝ) : Fin 3 → ℝ)), Set.finite_range _, ?_⟩
  have h := (Pi.basisFun ℝ (Fin 3)).span_eq
  rw [show (Set.range ⇑(Pi.basisFun ℝ (Fin 3)))
      = Set.range (fun i : Fin 3 => (Pi.single i (1 : ℝ) : Fin 3 → ℝ)) by
    ext v; simp [Pi.basisFun_apply]] at h
  exact h

end Chem

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

