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

theorem dioph_fin_dummies {n : ℕ} {S : Set (Vector3 ℕ n)} (d : Dioph S) :
    ∃ (m : ℕ) (p : Poly (Fin2 n ⊕ Fin2 m)), ∀ v, S v ↔ ∃ t : Vector3 ℕ m, p (v ⊗ t) = 0 := by
  classical
  obtain ⟨β, p, pe⟩ := d
  obtain ⟨s, hs⟩ := isPoly_support p.isPoly
  set sb : Finset β := s.biUnion (fun x => Sum.elim (fun _ => (∅ : Finset β)) (fun b => {b}) x)
    with hsb
  set m := sb.card with hm
  set e := sb.equivFin with he
  set f : β → Fin2 (m + 1) := fun b =>
    if h : b ∈ sb then Fin2.fs ((Fin2.equivFin m).symm (e ⟨b, h⟩)) else Fin2.fz with hf
  refine ⟨m + 1, Poly.map (Sum.map id f) p, fun v => ?_⟩
  have hcomp : ∀ (u : Vector3 ℕ (m + 1)),
      (Poly.map (Sum.map id f) p) (v ⊗ u) = p (v ⊗ (u ∘ f)) := by
    intro u
    rw [Poly.map_apply]
    congr 1
    funext x
    rcases x with a | b <;> rfl
  rw [pe v]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun j => Fin2.cases' 0 (fun j' => t (e.symm ((Fin2.equivFin m) j') : β)) j, ?_⟩
    rw [hcomp]
    rw [show p (v ⊗ ((fun j => Fin2.cases' 0
      (fun j' => t (e.symm ((Fin2.equivFin m) j') : β)) j) ∘ f)) = p (v ⊗ t) from ?_]
    · exact ht
    · refine hs _ _ ?_
      intro i hi
      rcases i with a | b
      · rfl
      · have hbsb : b ∈ sb := by
          rw [hsb]
          exact Finset.mem_biUnion.2 ⟨Sum.inr b, hi, by simp⟩
        show (fun j => Fin2.cases' 0 (fun j' => t (e.symm ((Fin2.equivFin m) j') : β)) j) (f b) = t b
        rw [hf]
        simp only [dif_pos hbsb]
        show t (e.symm ((Fin2.equivFin m) ((Fin2.equivFin m).symm (e ⟨b, hbsb⟩))) : β) = t b
        rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  · rintro ⟨u, hu⟩
    exact ⟨u ∘ f, by rw [← hcomp]; exact hu⟩

end H10

import Mathlib
import RequestProject.H10.Product
import RequestProject.H10.PolyAux

/-!
# The Davis–Putnam–Robinson bounded quantifier elimination (arithmetic core)

Here we prove the arithmetic equivalence underlying the theorem that Diophantine relations
are closed under bounded universal quantification:

`(∀ k < N, ∃ t, P (k, x, t) = 0)` holds if and only if there are numbers `c, Q, M, K, Y`
with `Q = W !` (for an explicit bound `W`), `M = ∏_{k<N} (1 + (k+1) Q)`,
`M ∣ Q K + Q + 1` (which forces `K ≡ k` modulo each factor), the residues of `Y` bounded
by `c`, and `M ∣ P (K, x, Y)`.

The Diophantine consequence is `H10.dioph_bounded_forall` in `RequestProject.H10.Forall`.
-/

namespace H10

open Nat Finset Dioph Vector3

local infixr:65 " ⊗ " => Sum.elim

