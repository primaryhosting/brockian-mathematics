import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
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

section Aumann

variable {Ω : Type*} [DecidableEq Ω]

/-- If `I` assigns to each state its information cell (so that the cells form a partition of the
state space), `M` is a union of cells, and `g` sums to zero over every cell meeting `M`, then `g`
sums to zero over `M`. -/

theorem sum_eq_zero_of_cells (I : Ω → Finset Ω)
    (hself : ∀ x, x ∈ I x) (hcell : ∀ x y, y ∈ I x → I y = I x) (g : Ω → ℝ) :
    ∀ M : Finset Ω, (∀ x ∈ M, I x ⊆ M) → (∀ x ∈ M, ∑ y ∈ I x, g y = 0) →
      ∑ y ∈ M, g y = 0 := by
  intro M
  induction M using Finset.strongInduction with
  | _ M ih =>
    intro hclosed hzero
    rcases M.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hIx : I x ⊆ M := hclosed x hx
      -- the rest `M \ I x` is again a union of cells
      have hsub : M \ I x ⊂ M := by
        refine Finset.ssubset_iff_of_subset (Finset.sdiff_subset) |>.2 ⟨x, hx, ?_⟩
        simp [hself x]
      have hclosed' : ∀ y ∈ M \ I x, I y ⊆ M \ I x := by
        intro y hy
        have hyM : y ∈ M := (Finset.mem_sdiff.1 hy).1
        have hyn : y ∉ I x := (Finset.mem_sdiff.1 hy).2
        intro z hz
        refine Finset.mem_sdiff.2 ⟨hclosed y hyM hz, ?_⟩
        intro hzIx
        -- if `z` lies in both cells, the cells coincide, contradicting `y ∉ I x`
        have h1 : I z = I y := hcell y z hz
        have h2 : I z = I x := hcell x z hzIx
        exact hyn (by rw [← h2, h1]; exact hself y)
      have hrest : ∑ y ∈ M \ I x, g y = 0 :=
        ih _ hsub hclosed' (fun y hy => hzero y (Finset.mem_sdiff.1 hy).1)
      have := Finset.sum_sdiff (f := g) hIx
      rw [← this, hrest, hzero x hx, add_zero]

/-- Conditional probabilities aggregate: if the posterior probability of `E` equals `q` on every
information cell contained in `M`, then it equals `q` on `M` itself. -/
