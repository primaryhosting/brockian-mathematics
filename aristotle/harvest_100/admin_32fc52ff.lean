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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-! ## Complexification -/

/-- Complex conjugation acting on the complexification `ℂ ⊗[ℚ] V` of a `ℚ`-vector space `V`,
as a `ℚ`-linear automorphism. -/
noncomputable def conjTensor (V : Type) [AddCommGroup V] [Module ℚ V] :
    (ℂ ⊗[ℚ] V) ≃ₗ[ℚ] (ℂ ⊗[ℚ] V) :=
  TensorProduct.congr (Complex.conjAe.toLinearEquiv.restrictScalars ℚ) (LinearEquiv.refl ℚ V)

@[simp] lemma conjTensor_tmul (V : Type) [AddCommGroup V] [Module ℚ V] (c : ℂ) (v : V) :
    conjTensor V (c ⊗ₜ[ℚ] v) = (starRingEnd ℂ) c ⊗ₜ[ℚ] v := rfl

/-- The canonical `ℚ`-linear inclusion `V → ℂ ⊗[ℚ] V`, `v ↦ 1 ⊗ v`. -/
noncomputable def incl (V : Type) [AddCommGroup V] [Module ℚ V] : V →ₗ[ℚ] ℂ ⊗[ℚ] V :=
  TensorProduct.mk ℚ ℂ V 1

@[simp] lemma incl_apply (V : Type) [AddCommGroup V] [Module ℚ V] (v : V) :
    incl V v = (1 : ℂ) ⊗ₜ[ℚ] v := rfl

lemma incl_injective (V : Type) [AddCommGroup V] [Module ℚ V] :
    Function.Injective (incl V) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ ℂ)
    (by
      rw [LinearMap.ker_eq_bot]
      exact fun a b h => by simpa using h)
  have hg1 : g 1 = 1 := by
    have := congrArg (fun f : ℚ →ₗ[ℚ] ℚ => f 1) hg
    simpa using this
  refine Function.LeftInverse.injective
    (g := fun x => (TensorProduct.lid ℚ V) (LinearMap.rTensor V g x)) ?_
  intro v
  simp [hg1]

/-! ## Rational Hodge structures with a subspace of algebraic classes -/

/--
A `HodgeDatum` packages the Hodge-theoretic data attached to a smooth projective complex
variety `X` in a fixed even cohomological degree `2p`:

* a finite-dimensional `ℚ`-vector space `V` (playing the role of `H^{2p}(X, ℚ)`);
* a decomposition of the complexification `ℂ ⊗[ℚ] V` into subspaces `H^{a,b}` indexed by
  pairs of integers, concentrated in bidegrees with `a + b = 2p` (purity), forming an
  internal direct sum, and exchanged by complex conjugation `H^{a,b} = conj H^{b,a}`;
* a `ℚ`-subspace `alg ⊆ V` (playing the role of the span of the classes of algebraic cycles
  of codimension `p` on `X`), which is required to consist of Hodge classes, i.e. of rational
  classes whose image in `ℂ ⊗[ℚ] V` lies in `H^{p,p}`.

The last requirement is the elementary half of the story: cycle classes are always Hodge
classes.  The Hodge conjecture is the converse inclusion, `HodgeConjecture` below.
-/
structure HodgeDatum where
  /-- The rational cohomology group `H^{2p}(X, ℚ)`. -/
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module ℚ V]
  /-- Half the weight: we look at `H^{2p}` and codimension `p` cycles. -/
  p : ℕ
  /-- The Hodge decomposition of the complexification. -/
  Hpq : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- Purity: the Hodge structure is pure of weight `2p`. -/
  pure' : ∀ ab : ℤ × ℤ, ab.1 + ab.2 ≠ 2 * (p : ℤ) → Hpq ab = ⊥
  /-- The pieces `H^{a,b}` decompose the complexification as an internal direct sum. -/
  internal : DirectSum.IsInternal Hpq
  /-- Complex conjugation exchanges `H^{a,b}` and `H^{b,a}`. -/
  conj_mem : ∀ (a b : ℤ) (x : ℂ ⊗[ℚ] V), x ∈ Hpq (a, b) → conjTensor V x ∈ Hpq (b, a)
  /-- The subspace of classes of algebraic cycles of codimension `p`. -/
  alg : Submodule ℚ V
  /-- Algebraic cycle classes are Hodge classes. -/
  alg_le : alg ≤ ((Hpq ((p : ℤ), (p : ℤ))).restrictScalars ℚ).comap (incl V)

attribute [instance] HodgeDatum.addCommGroup HodgeDatum.module

namespace HodgeDatum

variable (X : HodgeDatum)

/-- The space of *Hodge classes*: rational classes `v ∈ H^{2p}(X, ℚ)` whose image
`1 ⊗ v` in `ℂ ⊗[ℚ] H^{2p}(X, ℚ)` lies in the `(p,p)`-part of the Hodge decomposition. -/
noncomputable def hodgeClasses : Submodule ℚ X.V :=
  ((X.Hpq ((X.p : ℤ), (X.p : ℤ))).restrictScalars ℚ).comap (incl X.V)

lemma mem_hodgeClasses_iff (v : X.V) :
    v ∈ X.hodgeClasses ↔ (1 : ℂ) ⊗ₜ[ℚ] v ∈ X.Hpq ((X.p : ℤ), (X.p : ℤ)) := Iff.rfl

lemma alg_le_hodgeClasses : X.alg ≤ X.hodgeClasses := X.alg_le

end HodgeDatum

/--
**The Hodge conjecture** for the datum `X`: every Hodge class is a rational linear
combination of classes of algebraic cycles.
-/
def HodgeConjecture (X : HodgeDatum) : Prop := X.hodgeClasses ≤ X.alg

/-- Restated: the Hodge conjecture says exactly that the space of Hodge classes coincides
with the space of algebraic classes. -/
theorem hodgeConjecture_iff_eq (X : HodgeDatum) :
    HodgeConjecture X ↔ X.hodgeClasses = X.alg :=
  ⟨fun h => le_antisymm h X.alg_le_hodgeClasses, fun h => h.le⟩

/-- **Reduction to generators.** If some spanning set of the space of Hodge classes consists
of algebraic classes, then the Hodge conjecture holds for `X`. -/
theorem hodgeConjecture_of_span (X : HodgeDatum) (s : Set X.V)
    (hspan : Submodule.span ℚ s = X.hodgeClasses) (hs : ∀ v ∈ s, v ∈ X.alg) :
    HodgeConjecture X := by
  rw [HodgeConjecture, ← hspan, Submodule.span_le]
  exact hs

/-- **Transport along an isomorphism.** The Hodge conjecture only depends on the datum up
to isomorphism: if a `ℚ`-linear isomorphism identifies Hodge classes with Hodge classes and
algebraic classes with algebraic classes, it identifies the two instances of the conjecture. -/
theorem hodgeConjecture_congr (X Y : HodgeDatum) (e : X.V ≃ₗ[ℚ] Y.V)
    (hH : ∀ v : X.V, v ∈ X.hodgeClasses ↔ e v ∈ Y.hodgeClasses)
    (ha : ∀ v : X.V, v ∈ X.alg ↔ e v ∈ Y.alg) :
    HodgeConjecture X ↔ HodgeConjecture Y := by
  constructor
  · intro h w hw
    obtain ⟨v, rfl⟩ := e.surjective w
    exact (ha v).1 (h ((hH v).2 hw))
  · intro h v hv
    exact (ha v).2 (h ((hH v).1 hv))

/-- **Base case: no nonzero Hodge classes.** If the `(p,p)`-part of the Hodge decomposition
vanishes, there are no nonzero Hodge classes and the conjecture holds trivially. -/
theorem hodgeConjecture_of_Hpp_eq_bot (X : HodgeDatum)
    (h : X.Hpq ((X.p : ℤ), (X.p : ℤ)) = ⊥) : HodgeConjecture X := by
  intro v hv
  have hv' : (1 : ℂ) ⊗ₜ[ℚ] v ∈ X.Hpq ((X.p : ℤ), (X.p : ℤ)) := hv
  rw [h, Submodule.mem_bot] at hv'
  have hv0 : v = 0 := incl_injective X.V (by simpa using hv')
  rw [hv0]
  exact X.alg.zero_mem

/-- **Base case: `H^{2p}` of rank at most one.** If the cohomology group is at most
one-dimensional (e.g. `H^0` of a connected variety, or `H^{2n}` of an `n`-dimensional one)
and carries at least one nonzero algebraic class (e.g. the fundamental class, or the class
of a point), then the Hodge conjecture holds for `X`. -/
theorem hodgeConjecture_of_rank_le_one (X : HodgeDatum)
    (hrank : Module.rank ℚ X.V ≤ 1) (hne : X.alg ≠ ⊥) : HodgeConjecture X := by
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.1 hrank
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨r, hr⟩ := hv₀ a
  have hr0 : r ≠ 0 := by
    rintro rfl; exact ha0 (by simpa using hr.symm)
  have hv₀alg : v₀ ∈ X.alg := by
    have : v₀ = r⁻¹ • a := by
      rw [← hr, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [this]
    exact X.alg.smul_mem _ ha
  intro v _
  obtain ⟨s, hs⟩ := hv₀ v
  rw [← hs]
  exact X.alg.smul_mem _ hv₀alg

/-! ## Non-vacuity: the Hodge datum of a point -/

/-- The Hodge datum of a point (equivalently, `H^0` of a connected smooth projective
variety): `V = ℚ`, `p = 0`, the whole complexification sits in bidegree `(0,0)`, and the
fundamental class generates the algebraic classes. -/
noncomputable def pointDatum : HodgeDatum where
  V := ℚ
  p := 0
  Hpq := fun ab => if ab = (0, 0) then ⊤ else ⊥
  pure' := by
    rintro ⟨a, b⟩ h
    simp only [Nat.cast_zero, mul_zero] at h
    have hne : ((a, b) : ℤ × ℤ) ≠ (0, 0) := by
      intro hh
      rw [Prod.mk.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      simp at h
    simp [hne]
  internal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · intro i
      by_cases hi : i = (0, 0)
      · subst hi
        have hsup : (⨆ (j : ℤ × ℤ) (_ : j ≠ ((0 : ℤ), (0 : ℤ))),
            (fun ab : ℤ × ℤ => if ab = (0, 0) then (⊤ : Submodule ℂ (ℂ ⊗[ℚ] ℚ)) else ⊥) j)
            = ⊥ := by
          refine iSup_eq_bot.2 fun j => iSup_eq_bot.2 fun hj => ?_
          simp [hj]
        rw [hsup]
        exact disjoint_bot_right
      · have hbot : ((fun ab : ℤ × ℤ => if ab = (0, 0) then (⊤ : Submodule ℂ (ℂ ⊗[ℚ] ℚ)) else ⊥) i)
            = ⊥ := by simp [hi]
        rw [hbot]
        exact disjoint_bot_left
    · refine le_antisymm le_top ?_
      refine le_trans ?_ (le_iSup (fun j : ℤ × ℤ => if j = (0, 0) then
        (⊤ : Submodule ℂ (ℂ ⊗[ℚ] ℚ)) else ⊥) (0, 0))
      simp
  conj_mem := by
    intro a b x hx
    by_cases hab : (a, b) = (0, 0)
    · rw [Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      simp
    · have hx' : x ∈ (⊥ : Submodule ℂ (ℂ ⊗[ℚ] ℚ)) := by simpa [hab] using hx
      rw [Submodule.mem_bot] at hx'
      subst hx'
      simp
  alg := ⊤
  alg_le := le_top

/-- The Hodge conjecture holds for the datum of a point. -/
theorem hodgeConjecture_pointDatum : HodgeConjecture pointDatum := le_top

/-! ## The statement -/

/--
**Hodge statement.**

The Hodge conjecture, as formalized above, together with a Lean-checked reduction and the
verified base cases:

1. *(Formulation.)* For every Hodge datum `X` — a pure rational Hodge structure of weight
   `2p` on `H^{2p}(X, ℚ)` together with the subspace `alg` of classes of algebraic cycles of
   codimension `p`, which is contained in the space of Hodge classes — the Hodge conjecture
   for `X` is exactly the assertion that the space of Hodge classes equals the space of
   algebraic classes.
2. *(Non-vacuity / base case.)* There exists such a datum, namely that of a point, and the
   conjecture holds for it.
3. *(Reduction to generators.)* The conjecture for `X` follows from the algebraicity of any
   spanning set of the space of Hodge classes.
4. *(Invariance.)* The conjecture is invariant under isomorphisms of Hodge data.
5. *(Base case: vanishing `(p,p)`-part.)* If `H^{p,p} = 0` then the conjecture holds for `X`.
6. *(Base case: rank ≤ 1.)* If `H^{2p}(X, ℚ)` is at most one-dimensional and carries a
   nonzero algebraic class, then the conjecture holds for `X`.
-/
theorem hodge_statement :
    (∀ X : HodgeDatum, HodgeConjecture X ↔ X.hodgeClasses = X.alg) ∧
    (HodgeConjecture pointDatum) ∧
    (∀ (X : HodgeDatum) (s : Set X.V), Submodule.span ℚ s = X.hodgeClasses →
      (∀ v ∈ s, v ∈ X.alg) → HodgeConjecture X) ∧
    (∀ (X Y : HodgeDatum) (e : X.V ≃ₗ[ℚ] Y.V),
      (∀ v : X.V, v ∈ X.hodgeClasses ↔ e v ∈ Y.hodgeClasses) →
      (∀ v : X.V, v ∈ X.alg ↔ e v ∈ Y.alg) →
      (HodgeConjecture X ↔ HodgeConjecture Y)) ∧
    (∀ X : HodgeDatum, X.Hpq ((X.p : ℤ), (X.p : ℤ)) = ⊥ → HodgeConjecture X) ∧
    (∀ X : HodgeDatum, Module.rank ℚ X.V ≤ 1 → X.alg ≠ ⊥ → HodgeConjecture X) :=
  ⟨hodgeConjecture_iff_eq, hodgeConjecture_pointDatum, hodgeConjecture_of_span,
    hodgeConjecture_congr, hodgeConjecture_of_Hpp_eq_bot, hodgeConjecture_of_rank_le_one⟩

end Frontier

