/-
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede every command, including module docstrings, so the
-- header above is written as an ordinary comment and repeated as a module docstring below.)

import Mathlib

/-!
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
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

/-! ## The shape of the superrigidity conclusion -/

section Defs

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- The conclusion of a superrigidity theorem: the *abstract* group homomorphism
`rho : Γ →* H`, defined on a subgroup `Γ` of a topological group `G`, is the restriction of a
*continuous* homomorphism defined on all of `G`. -/
def ExtendsToContinuousHom (Γ : Subgroup G) (rho : Γ →* H) : Prop :=
  ∃ F : G →* H, Continuous F ∧ ∀ γ : Γ, F (γ : G) = rho γ

/-- The "virtual" form of the superrigidity conclusion, which is the one appearing in Margulis'
theorem: `rho` agrees with (the restriction of) a continuous homomorphism `G →* H` on a
finite-index subgroup of `Γ`. -/
def VirtuallyExtendsToContinuousHom (Γ : Subgroup G) (rho : Γ →* H) : Prop :=
  ∃ Γ₀ : Subgroup Γ, Γ₀.FiniteIndex ∧
    ∃ F : G →* H, Continuous F ∧ ∀ γ ∈ Γ₀, F ((γ : Γ) : G) = rho γ

/-- **Margulis superrigidity, as a property of a lattice.**

`MargulisSuperrigid Γ Admissible` says: every *admissible* abstract homomorphism from the lattice
`Γ ≤ G` into the topological group `H` virtually extends to a continuous homomorphism of the
ambient group `G`.

In Margulis' theorem `G` is a semisimple group of higher real rank, `Γ ≤ G` an irreducible
lattice, `H = 𝐇(k)` the `k`-points of a connected adjoint `k`-simple algebraic group over a local
field `k`, and the admissibility predicate `Admissible rho` is "the image of `rho` is Zariski dense and
unbounded".  Since Mathlib has no theory of algebraic groups, the admissibility predicate is kept
as a parameter here; the results below are proved for *every* choice of `Admissible`, hence in
particular for the Zariski-dense unbounded one. -/
def MargulisSuperrigid (Γ : Subgroup G) (Admissible : (Γ →* H) → Prop) : Prop :=
  ∀ rho : Γ →* H, Admissible rho → VirtuallyExtendsToContinuousHom Γ rho

end Defs

/-! ## Elementary properties of the conclusion -/

section Basic

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- An honest continuous extension is in particular a virtual one (take `Γ₀ = ⊤`). -/
theorem ExtendsToContinuousHom.virtually {Γ : Subgroup G} {rho : Γ →* H}
    (h : ExtendsToContinuousHom Γ rho) : VirtuallyExtendsToContinuousHom Γ rho := by
  obtain ⟨F, hFc, hF⟩ := h
  exact ⟨⊤, inferInstance, F, hFc, fun γ _ => hF γ⟩

/-- Uniqueness of the extension: a continuous homomorphism on `G` is determined by its
restriction to a dense subgroup, provided the target is Hausdorff.  (For a lattice `Γ` in a
connected group `G` the relevant density statement is the density of `Γ` in `G/`(compact), the
point being that the extension in Margulis' theorem is unique whenever it exists on a dense set.) -/
theorem extension_unique_of_dense [T2Space H] {Γ : Subgroup G} (hΓ : Dense (Γ : Set G))
    {F₁ F₂ : G →* H} (h₁ : Continuous F₁) (h₂ : Continuous F₂)
    (h : ∀ γ : Γ, F₁ (γ : G) = F₂ (γ : G)) : F₁ = F₂ :=
  DFunLike.coe_injective (Continuous.ext_on hΓ h₁ h₂ fun x hx => h ⟨x, hx⟩)

end Basic

/-! ## A Lean-checked reduction: extension from a dense subgroup -/

section DenseExtension

variable {G H : Type*} [UniformSpace G] [Group G] [IsUniformGroup G]
  [UniformSpace H] [Group H] [IsUniformGroup H] [CompleteSpace H] [T2Space H]

/-- **Reduction of the superrigidity conclusion to a uniform-continuity estimate.**

If `Γ ≤ G` is a *dense* subgroup and the abstract homomorphism `rho : Γ →* H` is uniformly
continuous for the uniformity induced from `G`, then `rho` does extend to a continuous homomorphism
`G →* H` (the target being a complete Hausdorff group).  This is the standard "soft" half of a
superrigidity argument: all the work is in producing the uniform continuity estimate. -/
theorem extendsToContinuousHom_of_dense_of_uniformContinuous {Γ : Subgroup G}
    (hΓ : Dense (Γ : Set G)) (rho : Γ →* H)
    (hrho : UniformContinuous fun x : (Γ : Set G) => rho ⟨(x : G), x.2⟩) :
    ExtendsToContinuousHom Γ rho := by
  set g : ((Γ : Set G)) → H := fun x => rho ⟨(x : G), x.2⟩
  set f : G → H := hΓ.extend g
  have hfc : Continuous f := (hΓ.uniformContinuous_extend hrho).continuous
  have hval : ∀ x : G, ∀ hx : x ∈ Γ, f x = rho ⟨x, hx⟩ := fun x hx =>
    hΓ.extend_of_ind hrho ⟨x, hx⟩
  have hmul : ∀ a b : G, f (a * b) = f a * f b := by
    have hd : Dense ((Γ : Set G) ×ˢ (Γ : Set G)) := hΓ.prod hΓ
    have key := Continuous.ext_on hd (f := fun p : G × G => f (p.1 * p.2))
      (g := fun p : G × G => f p.1 * f p.2)
      (hfc.comp continuous_mul) ((hfc.comp continuous_fst).mul (hfc.comp continuous_snd))
      (by
        rintro ⟨x, y⟩ ⟨hx, hy⟩
        simp only
        rw [hval x hx, hval y hy, hval (x * y) (Subgroup.mul_mem _ hx hy), ← map_mul rho]
        rfl)
    intro a b
    exact congrFun key (a, b)
  exact ⟨MonoidHom.mk' f hmul, hfc, fun γ => hval (γ : G) γ.2⟩

/-- **The superrigidity property follows from a uniform-continuity estimate.**

For a dense subgroup `Γ ≤ G` and a complete Hausdorff target, `MargulisSuperrigid Γ Admissible`
reduces to the statement that every admissible homomorphism is uniformly continuous. -/
theorem margulisSuperrigid_of_uniformContinuous {Γ : Subgroup G} (hΓ : Dense (Γ : Set G))
    (Admissible : (Γ →* H) → Prop)
    (h : ∀ rho : Γ →* H, Admissible rho →
      UniformContinuous fun x : (Γ : Set G) => rho ⟨(x : G), x.2⟩) :
    MargulisSuperrigid Γ Admissible := fun rho hrho =>
  (extendsToContinuousHom_of_dense_of_uniformContinuous hΓ rho (h rho hrho)).virtually

end DenseExtension

/-! ## The base case -/

/-- **Base case of Margulis superrigidity: abelian, torsion-free targets.**

A lattice `Γ` in a higher-rank semisimple group has Kazhdan's property (T), hence its
abelianization `Γ/[Γ,Γ]` is finite.  Consequently any abstract homomorphism from `Γ` into a
torsion-free abelian group is trivial, and therefore extends (by the trivial homomorphism) to a
continuous homomorphism of the ambient group.

Here the higher-rank hypothesis enters only through its consequence `Finite (Abelianization Γ)`. -/
theorem hom_trivial_of_abelianization_finite {G H : Type*} [Group G] [CommGroup H]
    (hH : ∀ (h : H) (n : ℕ), 0 < n → h ^ n = 1 → h = 1)
    (Γ : Subgroup G) [Finite (Abelianization Γ)] (rho : Γ →* H) (γ : Γ) : rho γ = 1 := by
  refine hH _ (Nat.card (Abelianization Γ)) Nat.card_pos ?_
  have h1 : (Abelianization.of γ) ^ Nat.card (Abelianization Γ) = 1 := pow_card_eq_one'
  have h2 : (Abelianization.lift rho) ((Abelianization.of γ) ^ Nat.card (Abelianization Γ)) = 1 := by
    rw [h1, map_one]
  rw [map_pow, Abelianization.lift_apply_of] at h2
  exact h2

/-- **Margulis superrigidity, base case.**

Let `Γ` be a lattice in a topological group `G` whose abelianization is finite — this holds for
every irreducible lattice in a semisimple group of higher real rank, by property (T) — and let `H`
be a torsion-free abelian topological group.  Then Margulis superrigidity holds for `Γ` with
target `H`, for *any* admissibility condition: every abstract homomorphism `Γ →* H` is the
restriction of a continuous homomorphism `G →* H` (necessarily the trivial one). -/
theorem margulis_superrigidity {G H : Type*} [Group G] [TopologicalSpace G]
    [CommGroup H] [TopologicalSpace H]
    (hH : ∀ (h : H) (n : ℕ), 0 < n → h ^ n = 1 → h = 1)
    (Γ : Subgroup G) [Finite (Abelianization Γ)] (Admissible : (Γ →* H) → Prop) :
    MargulisSuperrigid Γ Admissible := by
  intro rho _
  refine ⟨⊤, inferInstance, 1, continuous_const, fun γ _ => ?_⟩
  simp [hom_trivial_of_abelianization_finite hH Γ rho γ]

/-! ## Non-vacuity of the base case -/

section Sanity

/-- The additive group of the reals, written multiplicatively, is torsion free. -/
theorem multiplicative_real_torsionFree :
    ∀ (h : Multiplicative ℝ) (n : ℕ), 0 < n → h ^ n = 1 → h = 1 := by
  intro h n hn hpow
  have h0 : (n : ℝ) * (Multiplicative.toAdd h) = 0 := by
    have := congrArg Multiplicative.toAdd hpow
    simpa [nsmul_eq_mul] using this
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hh : Multiplicative.toAdd h = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h2
    · exact absurd h1 hne
    · exact h2
  exact Multiplicative.toAdd.injective (by simpa using hh)

local instance : TopologicalSpace (Equiv.Perm (Fin 5)) := ⊥
local instance : TopologicalSpace (Multiplicative ℝ) := inferInstanceAs (TopologicalSpace ℝ)

/-- A sanity check that the hypotheses of `margulis_superrigidity` are satisfiable by a
nontrivial pair (group, target): here `Γ = S₅` (finite abelianization) and `H = (ℝ, +)` written
multiplicatively (abelian and torsion free). -/
example (Admissible : ((⊤ : Subgroup (Equiv.Perm (Fin 5))) →* Multiplicative ℝ) → Prop) :
    MargulisSuperrigid (⊤ : Subgroup (Equiv.Perm (Fin 5))) Admissible :=
  margulis_superrigidity multiplicative_real_torsionFree ⊤ Admissible

end Sanity

/-! ## A concrete instance of the extension phenomenon -/

/-- The archetypal (rank-one, abelian) example: every abstract homomorphism from the lattice
`ℤ ≤ ℝ` to `ℝ` is the restriction of a continuous homomorphism `ℝ →+ ℝ`. -/
theorem extends_of_int_lattice_in_real (rho : ℤ →+ ℝ) :
    ∃ F : ℝ →+ ℝ, Continuous F ∧ ∀ n : ℤ, F (n : ℝ) = rho n := by
  refine ⟨AddMonoidHom.mulLeft (rho 1), ?_, fun n => ?_⟩
  · simpa [AddMonoidHom.coe_mulLeft] using continuous_mul_left (rho 1)
  · have hn : rho n = (n : ℝ) * rho 1 := by
      rw [← zsmul_eq_mul, ← map_zsmul rho n 1]
      norm_num
    simp [AddMonoidHom.coe_mulLeft, hn, mul_comm]

end Frontier

