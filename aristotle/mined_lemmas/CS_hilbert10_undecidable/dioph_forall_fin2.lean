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

theorem dioph_forall_fin2 {α : Type} : ∀ {m : ℕ} (S : Fin2 m → Set (α → ℕ)), (∀ j, Dioph (S j)) →
    Dioph {v | ∀ j, v ∈ S j}
  | 0, S, _ => by
      have h : {v : α → ℕ | ∀ j : Fin2 0, v ∈ S j} = Set.univ := by
        ext v; exact ⟨fun _ => trivial, fun _ j => nomatch j⟩
      rw [h]; exact dioph_univ
  | (m + 1), S, d => by
      have h := Dioph.inter (d Fin2.fz) (dioph_forall_fin2 (fun j => S (Fin2.fs j)) (fun j => d _))
      have e : {v : α → ℕ | ∀ j : Fin2 (m + 1), v ∈ S j} =
          (S Fin2.fz) ∩ {v | ∀ j : Fin2 m, v ∈ S (Fin2.fs j)} := by
        ext v
        exact ⟨fun hv => ⟨hv _, fun j => hv _⟩, fun ⟨h1, h2⟩ j => by cases j with
          | fz => exact h1
          | fs j => exact h2 j⟩
      rw [e]; exact h

