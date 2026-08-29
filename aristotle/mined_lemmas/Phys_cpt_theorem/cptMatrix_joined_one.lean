import Mathlib
/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
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

namespace Phys

/-- Complexified Minkowski spacetime: four complex coordinates. -/
abbrev Spacetime : Type := Fin 4 → ℂ

/-- The Minkowski metric `diag (1, -1, -1, -1)`, complexified. -/

theorem cptMatrix_joined_one : JoinedIn ComplexLorentzGroup 1 cptMatrix := by
  refine ⟨⟨⟨fun t => cptPath (t : ℝ), continuous_cptPath.comp continuous_subtype_val⟩, ?_, ?_⟩,
    ?_⟩
  · simpa using cptPath_zero
  · simpa using cptPath_one
  · intro t
    exact cptPath_mem _

/-- A local, Lorentz-invariant quantum field theory, presented through its
(analytically continued) Wightman functions. -/
structure LocalQFT where
  /-- The `n`-point Wightman function, continued to complexified spacetime. -/
  W : (n : ℕ) → (Fin n → Spacetime) → ℂ
  /-- Lorentz invariance. By the Bargmann–Hall–Wightman theorem, invariance of the
  Wightman functions under the real proper orthochronous Lorentz group, together with
  the spectral condition, extends by analytic continuation to invariance under the
  identity component of the *complex* Lorentz group; this is the form assumed here. -/
  lorentz_invariant : ∀ (n : ℕ) (L : Matrix (Fin 4) (Fin 4) ℂ),
    JoinedIn ComplexLorentzGroup 1 L → ∀ x : Fin n → Spacetime,
      W n (fun i => L.mulVec (x i)) = W n x
  /-- Locality, in the form of weak local commutativity: the Wightman functions are
  invariant under reversal of their arguments. -/
  local_commutativity : ∀ (n : ℕ) (x : Fin n → Spacetime),
    W n (fun i => x i.rev) = W n x

/-- **CPT theorem**: any Lorentz-invariant local quantum field theory is CPT invariant,
i.e. its Wightman functions satisfy
`W (x₁, …, xₙ) = W (-xₙ, …, -x₁)`. -/
