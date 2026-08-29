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

/-
The moduli `1 + (i+1)q` used to code finite sequences, and the Chinese remainder theorem
for them.
-/
import RequestProject.H10.Arith

open Dioph Finset

namespace H10

/-- The `i`-th modulus of the Chinese remainder coding with parameter `q`. -/

theorem dioph_normal {S : Set (α → ℕ)} (h : Dioph S) :
    ∃ (β : Type) (_ : Fintype β) (p : Poly (α ⊕ β)),
      ∀ v, v ∈ S ↔ ∃ t : β → ℕ, p (Sum.elim v t) = 0 := by
  classical
  obtain ⟨β, p, pe⟩ := h
  obtain ⟨s, C, d, hdep, -⟩ := IsPoly.spec p.isPoly
  set sb : Finset β := s.preimage Sum.inr (Sum.inr_injective.injOn) with hsb
  have hmem : ∀ b : β, b ∈ sb ↔ Sum.inr b ∈ s := by
    intro b; simp [hsb]
  refine ⟨{b : β // b ∈ sb}, inferInstance,
    ⟨fun w => p (fun c => ((Sum.elim (fun a => some (Sum.inl a))
      (fun b => if hb : b ∈ sb then some (Sum.inr ⟨b, hb⟩) else none)
        c : Option (α ⊕ _))).elim 0 w),
      IsPoly.subst p.isPoly _⟩, ?_⟩
  intro v
  refine Iff.trans (pe v) ?_
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun b => t b.1, ?_⟩
    refine Eq.trans ?_ ht
    refine hdep _ _ ?_
    rintro (a | b) hc
    · rfl
    · have : b ∈ sb := (hmem b).2 hc
      simp [this]
  · rintro ⟨t, ht⟩
    refine ⟨fun b => if hb : b ∈ sb then t ⟨b, hb⟩ else 0, ?_⟩
    refine Eq.trans ?_ ht
    refine hdep _ _ ?_
    rintro (a | b) hc
    · rfl
    · have : b ∈ sb := (hmem b).2 hc
      simp [this]

/-- A finite conjunction of Diophantine conditions is Diophantine. -/
