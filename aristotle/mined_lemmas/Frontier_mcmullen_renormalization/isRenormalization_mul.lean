/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-! ## Quadratic-like maps

Following Douady–Hubbard and McMullen, a *quadratic-like map* is a holomorphic proper
degree-two branched covering `f : U → V` between simply connected planar domains with
`closure U` a compact subset of `V`.  We encode "proper of degree two, branched over the
unique critical value" by the fibre conditions `fiber_crit` and `fiber_two`. -/

/-- A quadratic-like map `f : U → V` with critical point `c`. -/
structure QuadraticLike (f : ℂ → ℂ) (U V : Set ℂ) (c : ℂ) : Prop where
  /-- The domain is open. -/
  isOpen_U : IsOpen U
  /-- The range is open. -/
  isOpen_V : IsOpen V
  /-- `U` is relatively compact. -/
  isCompact_closure : IsCompact (closure U)
  /-- `U` is compactly contained in `V`. -/
  closure_subset : closure U ⊆ V
  /-- `f` is holomorphic on a neighbourhood of `V`. -/
  analytic : AnalyticOnNhd ℂ f V
  /-- `f` maps `U` into `V`. -/
  mapsTo : Set.MapsTo f U V
  /-- The critical point lies in `U`. -/
  crit_mem : c ∈ U
  /-- `c` is a critical point. -/
  crit_deriv : deriv f c = 0
  /-- The fibre over the critical value is the single (doubled) point `c`. -/
  fiber_crit : {z ∈ U | f z = f c} = {c}
  /-- Every other fibre consists of exactly two points: `f : U → V` is proper of degree 2. -/
  fiber_two : ∀ w ∈ V, w ≠ f c → ∃ a b : ℂ, a ≠ b ∧ {z ∈ U | f z = w} = {a, b}

/-- The filled Julia set of a quadratic-like map `f : U → V`:
points whose whole forward orbit stays in `U`. -/

theorem isRenormalization_mul {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {n m : ℕ}
    {U₁ V₁ U₂ V₂ : Set ℂ}
    (h₁ : IsRenormalization f U c n U₁ V₁)
    (h₂ : IsRenormalization (f^[n]) U₁ c m U₂ V₂) :
    IsRenormalization f U c (n * m) U₂ V₂ := by
  have hiter : f^[n * m] = (f^[n])^[m] := Function.iterate_mul f n m
  refine ⟨Nat.mul_pos h₁.pos h₂.pos, ?_, h₂.subset.trans h₁.subset, ?_, ?_⟩
  · rw [hiter]; exact h₂.quadraticLike
  · intro i hi
    -- write `i = n * q + r` with `r < n` and `q < m`
    have hn : 0 < n := h₁.pos
    set q := i / n with hq
    set r := i % n with hr
    have hir : n * q + r = i := Nat.div_add_mod i n
    have hrn : r < n := Nat.mod_lt _ hn
    have hqm : q < m := by
      by_contra hcon
      push_neg at hcon
      have : n * m ≤ n * q := Nat.mul_le_mul_left n hcon
      omega
    have hstep1 : Set.MapsTo ((f^[n])^[q]) U₂ U₁ := h₂.orbit q hqm
    have hstep2 : Set.MapsTo (f^[r]) U₁ U := h₁.orbit r hrn
    have : Set.MapsTo (f^[r] ∘ (f^[n])^[q]) U₂ U := hstep2.comp hstep1
    have hcomp : f^[r] ∘ (f^[n])^[q] = f^[i] := by
      rw [← Function.iterate_mul, ← Function.iterate_add]
      congr 1
      omega
    rwa [hcomp] at this
  · rw [hiter]; exact h₂.connected

/-- The multiplicative form on the level of period sets. -/
