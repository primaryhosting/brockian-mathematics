/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

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

/-!
## The setting

Mathlib does not (yet) contain the theory of smooth projective complex varieties,
singular cohomology with its Hodge decomposition, or the cycle class map.  We therefore
formalize the Hodge conjecture in the standard *linear-algebra* form it takes once the
geometric input is available:

* `V` plays the role of the singular cohomology group `H^{2p}(X, ℚ)` of a smooth
  projective complex variety `X`;
* `ℂ ⊗[ℚ] V` is its complexification `H^{2p}(X, ℂ)`;
* a `HodgeStructure V w` is a Hodge decomposition of weight `w` on `V`, i.e. a
  bigrading `H^{a,b}` of `ℂ ⊗[ℚ] V` concentrated in bidegrees with `a + b = w`
  and exchanged by complex conjugation;
* `hodgeClasses H p` is the ℚ-subspace of *Hodge classes*: rational classes whose
  image in the complexification lies in the `(p,p)` piece;
* an `AlgebraicClasses H p` is a subspace `A` of classes of algebraic cycles; the
  geometric fact that algebraic cycle classes are Hodge classes is recorded as the
  field `alg_le_hodge`.

The Hodge conjecture then reads: `hodgeClasses H p ≤ A`, i.e. every Hodge class is a
rational combination of classes of algebraic cycles.
-/

section Conjugation

variable (V : Type) [AddCommGroup V] [Module ℚ V]

/-- Complex conjugation on the complexification `ℂ ⊗[ℚ] V`, as a `ℚ`-linear map. -/

noncomputable def tateHodgeStructure (V : Type) [AddCommGroup V] [Module ℚ V] (p : ℤ) :
    HodgeStructure V (p + p) where
  F a b := if a = p ∧ b = p then ⊤ else ⊥
  weight a b hab := by
    have : ¬ (a = p ∧ b = p) := by rintro ⟨rfl, rfl⟩; exact hab rfl
    simp [this]
  indep := by
    intro ab
    by_cases h : ab.1 = p ∧ ab.2 = p
    · have hsup : (⨆ (cd : ℤ × ℤ) (_ : cd ≠ ab), if cd.1 = p ∧ cd.2 = p then
          (⊤ : Submodule ℂ (ℂ ⊗[ℚ] V)) else ⊥) = ⊥ := by
        refine iSup_eq_bot.2 fun cd => iSup_eq_bot.2 fun hcd => ?_
        by_cases h' : cd.1 = p ∧ cd.2 = p
        · exact absurd (Prod.ext (h'.1.trans h.1.symm) (h'.2.trans h.2.symm)) hcd
        · simp [h']
      simp only [hsup]
      exact disjoint_bot_right
    · simp only [h, if_false]
      exact disjoint_bot_left
  spanning := by
    refine top_le_iff.1 ?_
    refine le_trans ?_ (le_iSup (fun ab : ℤ × ℤ =>
      if ab.1 = p ∧ ab.2 = p then (⊤ : Submodule ℂ (ℂ ⊗[ℚ] V)) else ⊥) (p, p))
    simp
  conj_symm a b := by
    by_cases h : a = p ∧ b = p
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, if_true]
      rw [Submodule.restrictScalars_top, Submodule.map_top,
        LinearMap.range_eq_top.2 (conjC_surjective V)]
    · have h' : ¬ (b = p ∧ a = p) := fun hb => h ⟨hb.2, hb.1⟩
      simp [h, h']

