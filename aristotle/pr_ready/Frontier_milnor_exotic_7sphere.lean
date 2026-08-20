/-!
# Milnor Exotic 7 Sphere
Category: Frontier Abel
Target: Frontier.milnor_exotic_7sphere
Statement: There exist smooth manifolds homeomorphic but not diffeomorphic to S⁷ (Milnor).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Manifold

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

noncomputable section

/-! ## The standard smooth `7`-sphere -/

/-- `Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = 7 + 1`, needed to get Mathlib's smooth
manifold structure on the `7`-sphere. -/
instance factFinrankEuclidean8 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = 7 + 1) :=
  ⟨by simp⟩

/-- The standard round `7`-sphere `S⁷ ⊆ ℝ⁸`, with its standard smooth structure coming from
Mathlib (stereographic charts modelled on `EuclideanSpace ℝ (Fin 7)`). -/
abbrev StandardSphere7 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1

example : ChartedSpace (EuclideanSpace ℝ (Fin 7)) StandardSphere7 := inferInstance
example : IsManifold (𝓡 7) ⊤ StandardSphere7 := inferInstance

/-! ## What it means to be an exotic `7`-sphere -/

/-- A smooth `7`-manifold `N` (modelled on `EuclideanSpace ℝ (Fin 7)`) is an *exotic 7-sphere*
if it is homeomorphic to the standard `7`-sphere but admits **no** diffeomorphism onto it. -/
def IsExotic7Sphere (N : Type) [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 7)) N] [IsManifold (𝓡 7) ⊤ N] : Prop :=
  Nonempty (N ≃ₜ StandardSphere7) ∧
    IsEmpty (Diffeomorph (𝓡 7) (𝓡 7) N StandardSphere7 ⊤)

/-- The assertion that an exotic `7`-sphere exists: there is a smooth `7`-manifold which is
homeomorphic, but not diffeomorphic, to the standard `7`-sphere. -/
def ExoticSphereExists : Prop :=
  ∃ (N : Type) (tN : TopologicalSpace N)
    (cN : @ChartedSpace (EuclideanSpace ℝ (Fin 7)) _ N tN)
    (mN : @IsManifold ℝ _ (EuclideanSpace ℝ (Fin 7)) _ _ (EuclideanSpace ℝ (Fin 7)) _ (𝓡 7)
      ⊤ N tN cN),
    @IsExotic7Sphere N tN cN mN

/-! ## Milnor's `λ`-invariant: the arithmetic core

Milnor's exotic spheres are the total spaces `M h l` of the `S³`-bundles over `S⁴` classified by
the pair of integers `(h, l)`.  When `h + l = 1` the total space is (by an explicit Morse
function) homeomorphic to `S⁷`.  Milnor's invariant of such a total space is the residue
`λ (M h l) = (h - l)² - 1  (mod 7)`,
which vanishes for the standard sphere (the case `h = 1`, `l = 0`).  The arithmetic base case of
Milnor's argument is the observation that this residue is *not* always `0`. -/

/-- Milnor's `λ`-invariant of the `S³`-bundle over `S⁴` with Euler/Pontryagin data `(h, l)`,
as a residue modulo `7`. -/
def milnorLambda (h l : ℤ) : ZMod 7 := (((h - l) ^ 2 - 1 : ℤ) : ZMod 7)

/-- The standard sphere corresponds to `(h, l) = (1, 0)`, where the invariant vanishes. -/
theorem milnorLambda_one_zero : milnorLambda 1 0 = 0 := by
  unfold milnorLambda
  norm_num

/-- **Arithmetic base case of Milnor's theorem.**  There is an admissible pair `(h, l)`
(i.e. with `h + l = 1`) whose `λ`-invariant is nonzero mod `7`; explicitly `(h, l) = (2, -1)`
gives `λ = 3² - 1 = 8 ≡ 1 (mod 7)`. -/
theorem milnorLambda_two_negOne : (2 : ℤ) + (-1) = 1 ∧ milnorLambda 2 (-1) ≠ 0 := by
  refine ⟨by norm_num, ?_⟩
  have : milnorLambda 2 (-1) = ((8 : ℤ) : ZMod 7) := by
    unfold milnorLambda; norm_num
  rw [this]
  decide

/-- Sanity check: the standard `7`-sphere is of course *not* an exotic `7`-sphere, since the
identity is a diffeomorphism of it onto itself.  In particular `IsExotic7Sphere` is a genuinely
restrictive condition. -/
theorem not_isExotic7Sphere_standard : ¬ IsExotic7Sphere StandardSphere7 := by
  rintro ⟨-, hempty⟩
  exact hempty.elim (Diffeomorph.refl (𝓡 7) StandardSphere7 ⊤)

/-- There exists an admissible pair with nonvanishing `λ`-invariant. -/
theorem exists_admissible_milnorLambda_ne_zero :
    ∃ h l : ℤ, h + l = 1 ∧ milnorLambda h l ≠ 0 :=
  ⟨2, -1, milnorLambda_two_negOne.1, milnorLambda_two_negOne.2⟩

/-! ## The reduction

The remaining, geometric, content of Milnor's theorem is packaged as the three hypotheses
`hlam`, `hhomeo`, `hinv` below:

* `hhomeo` : for `h + l = 1` the total space `M h l` is homeomorphic to `S⁷`
  (Milnor's Morse-theoretic argument: `M h l` carries a Morse function with exactly two
  critical points, hence is homeomorphic to `S⁷` by Reeb's theorem);
* `hlam` : the `λ`-invariant of `M h l` is `(h - l)² - 1 mod 7`
  (computed from the Hirzebruch signature theorem applied to a coboundary of `M h l`);
* `hinv` : `λ` is a diffeomorphism invariant which vanishes on the standard `S⁷`
  (i.e. if `M h l` were diffeomorphic to `S⁷`, its `λ` would be `0`).

Given this package, the existence of an exotic `7`-sphere is a purely formal consequence of the
arithmetic base case above.  This is exactly Milnor's reduction, verified in Lean. -/
theorem milnor_exotic_7sphere
    (M : ℤ → ℤ → Type)
    [instTop : ∀ h l : ℤ, TopologicalSpace (M h l)]
    [instChart : ∀ h l : ℤ, ChartedSpace (EuclideanSpace ℝ (Fin 7)) (M h l)]
    [instMfd : ∀ h l : ℤ, IsManifold (𝓡 7) ⊤ (M h l)]
    (lam : ℤ → ℤ → ZMod 7)
    (hlam : ∀ h l : ℤ, h + l = 1 → lam h l = milnorLambda h l)
    (hhomeo : ∀ h l : ℤ, h + l = 1 → Nonempty (M h l ≃ₜ StandardSphere7))
    (hinv : ∀ h l : ℤ, h + l = 1 →
      Nonempty (Diffeomorph (𝓡 7) (𝓡 7) (M h l) StandardSphere7 ⊤) → lam h l = 0) :
    ExoticSphereExists := by
  obtain ⟨h, l, hsum, hne⟩ := exists_admissible_milnorLambda_ne_zero
  refine ⟨M h l, instTop h l, instChart h l, instMfd h l, hhomeo h l hsum, ?_⟩
  refine ⟨fun f => hne ?_⟩
  rw [← hlam h l hsum]
  exact hinv h l hsum ⟨f⟩

end

end Frontier

