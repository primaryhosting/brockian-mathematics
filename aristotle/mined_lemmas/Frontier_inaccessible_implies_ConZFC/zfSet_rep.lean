import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## The first-order language of set theory

We build the first-order language with a single binary relation symbol `∈`, write down a
standard axiomatization of `ZFC` in it (extensionality, empty set, pairing, union, power set,
infinity, foundation, choice, together with the separation and replacement schemes), and prove
that Mathlib's type `ZFSet` of ZFC-sets is a model of this theory.
-/

namespace Frontier

open FirstOrder Language

universe u

/-- The relation symbols of the language of set theory: a single binary relation. -/
inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

/-- The first-order language of set theory. -/

theorem zfSet_rep {k : ℕ} (φ : setLang.Formula (Fin (k + 2))) : ZFSet.{u} ⊨ repAx φ := by
  simp only [repAx, Sentence.Realize, BoundedFormula.realize_alls, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_iff,
    BoundedFormula.realize_inf, realize_memF, realize_eqF, realize_subst₀,
    snoc3_gRep₁, snoc4_gRep₂, snoc4_gRep₃, snoc2_k, snoc2_k1, snoc4_k]
  intro xs a hfun
  have hfun' : ∀ x : ZFSet.{u}, ∃ y : ZFSet.{u}, x ∈ a →
      (φ.Realize (extVal₂ x y xs) ∧ ∀ y', φ.Realize (extVal₂ x y' xs) → y' = y) := by
    intro x
    by_cases hx : x ∈ a
    · obtain ⟨y, hy⟩ := hfun x hx
      exact ⟨y, fun _ => hy⟩
    · exact ⟨∅, fun h => absurd h hx⟩
  choose f hf using hfun'
  refine ⟨ZFSet.image f a, fun y => ⟨?_, ?_⟩⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := ZFSet.mem_image.1 hy
    exact ⟨x, hx, (hf x hx).1⟩
  · rintro ⟨x, hx, hP⟩
    exact ZFSet.mem_image.2 ⟨x, hx, ((hf x hx).2 y hP).symm⟩

/-- `ZFSet` is a model of `ZFC`. -/
instance zfSet_models_ZFC : ZFSet.{u} ⊨ ZFC := by
  refine ⟨?_⟩
  rintro ψ ((h | ⟨k, φ, rfl⟩) | ⟨k, φ, rfl⟩)
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact zfSet_extensionality
    · exact zfSet_emptySet
    · exact zfSet_pairing
    · exact zfSet_union
    · exact zfSet_powerSet
    · exact zfSet_infinity
    · exact zfSet_foundation
    · exact zfSet_choice
  · exact zfSet_sep φ
  · exact zfSet_rep φ

/-- `ZFC` is satisfiable, i.e. `Con(ZFC)` holds: `ZFSet` is a model. -/
