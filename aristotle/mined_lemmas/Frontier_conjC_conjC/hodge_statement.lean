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

theorem hodge_statement :
    (∀ (V : Type) [AddCommGroup V] [Module ℚ V] (w : ℤ) (H : HodgeStructure V w) (p : ℤ)
        (C : AlgebraicClasses H p),
        HodgeConjectureFor H p C ↔ ¬ ∃ v : V, v ∈ hodgeClasses H p ∧ v ∉ C.A) ∧
    (∀ (V : Type) [AddCommGroup V] [Module ℚ V] (w : ℤ) (H : HodgeStructure V w) (p : ℤ)
        (C : AlgebraicClasses H p),
        HodgeConjectureFor H p C ↔ hodgeClasses H p = C.A) ∧
    (∀ (V : Type) [AddCommGroup V] [Module ℚ V] (w : ℤ) (H : HodgeStructure V w) (p : ℤ)
        (C : AlgebraicClasses H p),
        HodgeConjectureFor H p C ↔
          ∃ S : Set V, S ⊆ (C.A : Set V) ∧ Submodule.span ℚ S = hodgeClasses H p) ∧
    (∀ (V : Type) [AddCommGroup V] [Module ℚ V] (w : ℤ) (H : HodgeStructure V w) (p : ℤ),
        p + p ≠ w → hodgeClasses H p = ⊥ ∧
          ∀ C : AlgebraicClasses H p, HodgeConjectureFor H p C) ∧
    (∀ (V : Type) [AddCommGroup V] [Module ℚ V] (p : ℤ),
        hodgeClasses (tateHodgeStructure V p) p = ⊤) ∧
    (∀ C : AlgebraicClasses (tateHodgeStructure ℚ 0) 0, C.A = ⊤ →
        HodgeConjectureFor (tateHodgeStructure ℚ 0) 0 C) ∧
    (∀ (V V' : Type) [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']
        (w w' : ℤ) (H : HodgeStructure V w) (H' : HodgeStructure V' w') (p : ℤ)
        (f : V →ₗ[ℚ] V'), IsHodgeMorphism H H' f →
          (hodgeClasses H p).map f ≤ hodgeClasses H' p) ∧
    (∀ (V V' : Type) [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']
        (w w' : ℤ) (H : HodgeStructure V w) (H' : HodgeStructure V' w') (p : ℤ)
        (f : V →ₗ[ℚ] V') (C : AlgebraicClasses H p) (C' : AlgebraicClasses H' p),
        hodgeClasses H' p ≤ (hodgeClasses H p).map f → C.A.map f ≤ C'.A →
          HodgeConjectureFor H p C → HodgeConjectureFor H' p C') := by
  refine ⟨fun V _ _ w H p C => hodgeConjectureFor_iff_not_exists H p C,
    fun V _ _ w H p C => hodgeConjectureFor_iff_eq H p C,
    fun V _ _ w H p C => hodgeConjectureFor_iff_span H p C,
    fun V _ _ w H p hpw =>
      ⟨hodgeClasses_eq_bot_of_F_eq_bot H p (H.weight p p hpw),
        fun C => hodgeConjectureFor_of_two_mul_ne H p hpw C⟩,
    fun V _ _ p => hodgeClasses_tate V p,
    fun C hC => hodgeConjectureFor_degree_zero C hC,
    fun V V' _ _ _ _ w w' H H' p f hf => map_hodgeClasses_le hf p,
    fun V V' _ _ _ _ w w' H H' p f C C' hsurj hA hHC =>
      hodgeConjectureFor_of_morphism C C' hsurj hA hHC⟩

end Frontier

