import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.Weyl.SchrodingerMinimal

open LinearPMap

open scoped LinearPMap ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A densely defined operator `T` on a complex Hilbert space is *essentially self-adjoint* if
its adjoint is self-adjoint; equivalently, `T` has a unique self-adjoint extension, namely the
closure `T†† = T̄` of `T`. -/

theorem essentiallySelfAdjoint_of_deficiency {T : H →ₗ.[ℂ] H} (hdense : Dense (T.domain : Set H))
    (hsymm : T.IsFormalAdjoint T)
    (hpos : ∀ (u : H) (hu : u ∈ (T†).domain), T† ⟨u, hu⟩ = Complex.I • u → u = 0)
    (hneg : ∀ (u : H) (hu : u ∈ (T†).domain), T† ⟨u, hu⟩ = -Complex.I • u → u = 0) :
    EssentiallySelfAdjoint T := by
  have hd' : Dense ((T†).domain : Set H) := dense_adjoint_domain hdense hsymm
  have hAle : T†† ≤ T† := adjoint_adjoint_le_adjoint hdense hsymm
  have hTA : T ≤ T†† := le_adjoint_adjoint hdense hsymm
  have hAclosed : (T††).IsClosed := adjoint_isClosed hd'
  have hAsymm : (T††).IsFormalAdjoint (T††) := adjoint_adjoint_isFormalAdjoint hdense hsymm
  -- the range of `T + i` is dense
  have hKbot : (LinearMap.range (shiftMap T Complex.I))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := (mem_orthogonal_range_shiftMap_iff hdense Complex.I v).mp hv
    refine hpos v hv1 ?_
    rw [hv2]
    simp
  have hKdense : Dense ((LinearMap.range (shiftMap T Complex.I) : Submodule ℂ H) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact Submodule.topologicalClosure_eq_top_iff.mpr hKbot
  have hdenseRange :
      Dense (Set.range fun x : (T††).domain => T†† x + Complex.I • (x : H)) := by
    refine hKdense.mono ?_
    rintro w ⟨x, rfl⟩
    exact ⟨⟨(x : H), hTA.1 x.2⟩, by
      simp only [shiftMap_apply]
      rw [← hTA.2 (rfl : ((x : H)) = ((⟨(x : H), hTA.1 x.2⟩ : (T††).domain) : H))]⟩
  -- surjectivity of `T†† + i`
  have hsurj : ∀ y : H, ∃ x : (T††).domain, T†† x + Complex.I • (x : H) = y := by
    intro y
    refine surjective_shift_of_isClosed hAclosed hAsymm ?_ ?_ hdenseRange y
    · simp
    · simp
  -- conclude
  have hle2 : T† ≤ T†† := by
    constructor
    · intro u hu
      obtain ⟨v, hv⟩ := hsurj (T† ⟨u, hu⟩ + Complex.I • u)
      have hvT : (v : H) ∈ (T†).domain := hAle.1 v.2
      have hvval : T† (⟨(v : H), hvT⟩ : (T†).domain) = T†† v :=
        (hAle.2 (rfl : ((v : H)) = ((⟨(v : H), hvT⟩ : (T†).domain) : H))).symm
      have hw : (⟨u, hu⟩ : (T†).domain) - ⟨(v : H), hvT⟩ = ⟨u - (v : H), by
        exact Submodule.sub_mem _ hu hvT⟩ := rfl
      have hTw : T† (⟨u - (v : H), Submodule.sub_mem _ hu hvT⟩ : (T†).domain)
          = -Complex.I • (u - (v : H)) := by
        have := (T†).map_sub (⟨u, hu⟩ : (T†).domain) ⟨(v : H), hvT⟩
        rw [hw] at this
        rw [this, hvval, ← hv]
        simp only [smul_sub]
        module
      have hzero : u - (v : H) = 0 := hneg _ _ hTw
      have : u = (v : H) := by
        have := sub_eq_zero.mp hzero
        exact this
      rw [this]
      exact v.2
    · intro x y hxy
      -- `x : T†.domain`, `y : T††.domain`, `(x : H) = y`
      exact (hAle.2 hxy.symm).symm
  have : T†† = T† := le_antisymm hAle hle2
  exact this

/-- The Hilbert space `L²(ℝ, ℂ)` on which the Schrödinger operator acts. -/
abbrev L2R : Type := MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)

/-- **Essential self-adjointness of the minimal Schrödinger operator from the ODE (Weyl limit
point) hypothesis.**

Here `T` is the minimal Schrödinger operator `u ↦ -u'' + V u` on `L²(ℝ)`, given as a densely
defined symmetric (`T.IsFormalAdjoint T`) unbounded operator, e.g. defined on `C_c^∞(ℝ)`.

The elements `u` of the domain of the adjoint `T†` with `T† u = ± i u` are exactly the
square-integrable (weak) solutions of the Schrödinger ODE `-u'' + V u = ± i u`; the hypotheses
`hode_pos` and `hode_neg` state that this ODE has no nonzero `L²` solution, which is Weyl's
limit-point condition.  Under this hypothesis `T` is essentially self-adjoint: its adjoint is
self-adjoint, i.e. `T†† = T†`, so the closure `T†† = T̄` of `T` is the unique self-adjoint
extension of `T`. -/
