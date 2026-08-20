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

set_option grind.warning false

namespace Chem

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₈`. -/

lemma adjMatrix_mul_Pv : ((SimpleGraph.cycleGraph 8).adjMatrix ℂ) * Pv = Pv * Dg := by
  ext i k
  have hL : (((SimpleGraph.cycleGraph 8).adjMatrix ℂ) * Pv) i k = Pv (i - 1) k + Pv (i + 1) k := by
    rw [Matrix.mul_apply,
      show (∑ j, ((SimpleGraph.cycleGraph 8).adjMatrix ℂ) i j * Pv j k)
        = (((SimpleGraph.cycleGraph 8).adjMatrix ℂ) *ᵥ (fun j => Pv j k)) i from rfl,
      adj8_mulVec]
  have e1 : om ^ ((i - 1 : Fin 8) * k : ℕ) = om ^ ((i : ℕ) * k + 7 * k) := by
    apply om_pow_mod
    have hv : ((i - 1 : Fin 8) : ℕ) = ((i : ℕ) + 7) % 8 := by rw [Fin.sub_def]; simp [Nat.add_comm]
    rw [hv, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
      show ((i : ℕ) + 7) * (k : ℕ) = (i : ℕ) * (k : ℕ) + 7 * (k : ℕ) from by ring]
  have e2 : om ^ ((i + 1 : Fin 8) * k : ℕ) = om ^ ((i : ℕ) * k + k) := by
    apply om_pow_mod
    have hv : ((i + 1 : Fin 8) : ℕ) = ((i : ℕ) + 1) % 8 := by rw [Fin.add_def]; simp
    rw [hv, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
      show ((i : ℕ) + 1) * (k : ℕ) = (i : ℕ) * (k : ℕ) + (k : ℕ) from by ring]
  rw [hL, Dg, Matrix.mul_diagonal, Pv_apply, Pv_apply, Pv_apply, ← om_sum, e1, e2, pow_add, pow_add]
  ring

open Polynomial in
