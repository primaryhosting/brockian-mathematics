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

import Mathlib
import RequestProject.H10.Factorial

/-!
# The product `∏_{k=1}^{y} (a + b*k)` is Diophantine

This is the last of the classical auxiliary Diophantine functions needed for the
Davis–Putnam–Robinson elimination of bounded universal quantifiers.

The idea is that modulo a large `N` coprime to `b`, one has
`∏_{k=1}^{y} (a + b k) ≡ b^y ∏_{k=1}^{y} (m + k) = b^y y! binom(m+y, y)`
where `m` is the residue `a * b⁻¹ mod N`.
-/

namespace H10

open Nat Finset Dioph

/-- `prodAB a b y = (a + b) * (a + 2b) * ⋯ * (a + y b)`. -/

theorem dioph_bounded_forall {n : ℕ} {S : Set (Vector3 ℕ (n + 1))} (d : Dioph S) :
    Dioph {v : Vector3 ℕ (n + 1) | ∀ k < v fz, (k :: (v ∘ fs)) ∈ S} := by
  obtain ⟨m, pp, pe⟩ := dioph_fin_dummies d
  obtain ⟨q, hqp, hqb, hqm⟩ := isPoly_majorant pp.isPoly
  set qq : Poly (Fin2 (n + 1) ⊕ Fin2 m) := ⟨q, hqp⟩ with hqq
  set mp1 : Fin2 (n + 1) ⊕ Fin2 m → Fin2 (n + 1) ⊕ (Fin2 4 ⊕ Fin2 m) :=
    Sum.elim (fun i => Sum.inl i) (fun _ => Sum.inr (Sum.inl &0)) with hmp1
  set mp2 : Fin2 (n + 1) ⊕ Fin2 m → Fin2 (n + 1) ⊕ (Fin2 4 ⊕ Fin2 m) :=
    Sum.elim (fun a => Fin2.cases' (Sum.inr (Sum.inl &3)) (fun i => Sum.inl (Fin2.fs i)) a)
      (fun j => Sum.inr (Sum.inr j)) with hmp2
  have hcond : Dioph {w : (Fin2 (n + 1) ⊕ (Fin2 4 ⊕ Fin2 m)) → ℕ |
      (w (inr (inl &1)) = (((Poly.map mp1 qq) w).natAbs + w (inr (inl &0)) + w (inl fz))!) ∧
      (w (inr (inl &2)) = prodAB 1 (w (inr (inl &1))) (w (inl fz))) ∧
      (w (inr (inl &2)) ∣ w (inr (inl &1)) * w (inr (inl &3)) + w (inr (inl &1)) + 1) ∧
      (∀ j : Fin2 m, w (inr (inl &0)) ≤ w (inr (inr j)) ∧
        w (inr (inl &2)) ∣ (w (inr (inr j))).descFactorial (w (inr (inl &0)) + 1)) ∧
      (w (inr (inl &2)) ∣ ((Poly.map mp2 pp) w).natAbs)} := by
    refine ((Dioph.proj_dioph (inr (inl &1))) D= (dioph_factorial
      (((Dioph.abs_poly_dioph (Poly.map mp1 qq)) D+ (Dioph.proj_dioph (inr (inl &0))))
        D+ (Dioph.proj_dioph (inl fz))))) D∧ ?_
    refine ((Dioph.proj_dioph (inr (inl &2))) D= (dioph_prodAB (D.1)
      (Dioph.proj_dioph (inr (inl &1))) (Dioph.proj_dioph (inl fz)))) D∧ ?_
    refine ((Dioph.proj_dioph (inr (inl &2))) D∣ (((Dioph.proj_dioph (inr (inl &1)))
      D* (Dioph.proj_dioph (inr (inl &3)))) D+ (Dioph.proj_dioph (inr (inl &1))) D+ (D.1))) D∧ ?_
    refine (dioph_forall_fin2 _ (fun j => ?_)) D∧
      ((Dioph.proj_dioph (inr (inl &2))) D∣ (Dioph.abs_poly_dioph (Poly.map mp2 pp)))
    exact ((Dioph.proj_dioph (inr (inl &0))) D≤ (Dioph.proj_dioph (inr (inr j)))) D∧
      ((Dioph.proj_dioph (inr (inl &2))) D∣
        (dioph_descFactorial (Dioph.proj_dioph (inr (inr j)))
          ((Dioph.proj_dioph (inr (inl &0))) D+ (D.1))))
  refine Dioph.ext (Dioph.ex_dioph hcond) (fun v => ?_)
  have hv1 : ∀ (z : (Fin2 4 ⊕ Fin2 m) → ℕ),
      ((v ⊗ z) ∘ mp1) = ((v fz :: (v ∘ fs)) ⊗ (fun _ => z (inl &0))) := by
    intro z
    funext y
    rcases y with a | j
    · cases a with
      | fz => rfl
      | fs a => rfl
    · rfl
  have hv2 : ∀ (z : (Fin2 4 ⊕ Fin2 m) → ℕ),
      ((v ⊗ z) ∘ mp2) = ((z (inl &3) :: (v ∘ fs)) ⊗ (fun j => z (inr j))) := by
    intro z
    funext y
    rcases y with a | j
    · cases a with
      | fz => rfl
      | fs a => rfl
    · rfl
  constructor
  · rintro ⟨z, h1, h2, h3, h4, h5⟩
    rw [Poly.map_apply, hv1 z] at h1
    rw [Poly.map_apply, hv2 z] at h5
    intro k hk
    refine (pe _).2 ?_
    refine dpr_of_exists pp.isPoly hqb hqm (v fz) (v ∘ fs)
      (z (inl &0)) (z (inl &1)) (z (inl &2)) (z (inl &3)) (fun j => z (inr j))
      h1 h2 h3 h4 h5 k hk
  · intro H
    obtain ⟨c, Q, M, K, Y, e1, e2, e3, e4, e5⟩ :=
      exists_of_dpr (q := q) pp.isPoly (v fz) (v ∘ fs)
        (fun k hk => (pe _).1 (H k hk))
    refine ⟨Sum.elim [c, Q, M, K] Y, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Poly.map_apply, hv1 _]; exact e1
    · exact e2
    · exact e3
    · exact e4
    · rw [Poly.map_apply, hv2 _]; exact e5

end H10

