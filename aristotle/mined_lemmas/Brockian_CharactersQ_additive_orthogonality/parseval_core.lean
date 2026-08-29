import Mathlib

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

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Tactic

/-!
# Fourier analysis and characters on `ZMod q`

The reusable, general-modulus character kernel needed by the analytic large-sieve and
Bombieri--Vinogradov layers.  This module deliberately wraps Mathlib's canonical
`ZMod.stdAddChar`, `ZMod.dft`, and `DirichletCharacter`; it introduces no competing
character convention.
-/

open scoped BigOperators

noncomputable section

namespace Brockian.CharactersQ

variable (q : ℕ) [NeZero q]

/-- Mathlib's canonical additive character `x ↦ exp (2πix/q)`. -/
abbrev additiveChar : AddChar (ZMod q) ℂ := ZMod.stdAddChar

/-- Complex Dirichlet characters modulo `q`, reused from Mathlib. -/
abbrev MultiplicativeChar := DirichletCharacter ℂ q

/-- The unnormalised discrete Fourier transform on `ZMod q`. -/

private theorem parseval_core (f : ZMod q → ℂ) :
    ∑ a : ZMod q, fourier q f a * (starRingEnd ℂ) (fourier q f a) =
      (q : ℂ) * ∑ x : ZMod q, f x * (starRingEnd ℂ) (f x) := by
  have hexp : ∀ a : ZMod q,
      fourier q f a * (starRingEnd ℂ) (fourier q f a) =
        ∑ x : ZMod q, ∑ y : ZMod q,
          f x * (starRingEnd ℂ) (f y) * additiveChar q (a * (y - x)) := by
    intro a
    rw [fourier_apply, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    have key : additiveChar q (-(x * a)) * additiveChar q (- -(y * a)) =
        additiveChar q (a * (y - x)) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [map_mul, conj_additiveChar]
    linear_combination (f x * (starRingEnd ℂ) (f y)) * key
  rw [Finset.sum_congr rfl (fun a _ => hexp a)]
  rw [Finset.sum_comm]
  have hdiag : ∀ x : ZMod q,
      ∑ a : ZMod q, ∑ y : ZMod q,
          f x * (starRingEnd ℂ) (f y) * additiveChar q (a * (y - x)) =
        (q : ℂ) * (f x * (starRingEnd ℂ) (f x)) := by
    intro x
    rw [Finset.sum_comm]
    have hin : ∀ y : ZMod q,
        ∑ a : ZMod q,
            f x * (starRingEnd ℂ) (f y) * additiveChar q (a * (y - x)) =
          if y = x then (q : ℂ) * (f x * (starRingEnd ℂ) (f y)) else 0 := by
      intro y
      rw [← Finset.mul_sum]
      rw [additive_orthogonality_sub]
      by_cases h : y = x
      · subst h
        simp [mul_comm]
      · simp [h]
    rw [Finset.sum_congr rfl (fun y _ => hin y), Finset.sum_ite_eq' Finset.univ x]
    simp
  rw [Finset.sum_congr rfl (fun x _ => hdiag x), ← Finset.mul_sum]

/-- Parseval/Plancherel for the unnormalised DFT on every nonzero modulus. -/
