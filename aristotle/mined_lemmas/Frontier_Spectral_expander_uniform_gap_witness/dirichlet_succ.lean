/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

/-! ## The hypercube graph -/

/-- Flip the `i`-th coordinate of a point of the discrete cube `Fin k → Bool`. -/

lemma dirichlet_succ {k : ℕ} (f : (Fin (k + 1) → Bool) → ℝ) :
    dirichlet (k + 1) f
      = dirichlet k (fun y => f (Fin.cons false y)) + dirichlet k (fun y => f (Fin.cons true y))
        + 2 * ∑ y : Fin k → Bool,
            (f (Fin.cons false y) - f (Fin.cons true y)) ^ 2 := by
  have key : ∀ (b : Bool) (y : Fin k → Bool),
      (∑ i : Fin (k + 1), (f (Fin.cons b y) - f (flipAt i (Fin.cons b y))) ^ 2)
        = (f (Fin.cons b y) - f (Fin.cons (!b) y)) ^ 2
          + ∑ i : Fin k, (f (Fin.cons b y) - f (Fin.cons b (flipAt i y))) ^ 2 := by
    intro b y
    rw [Fin.sum_univ_succ, flipAt_zero_cons]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [flipAt_succ_cons]
  have hswap : ∑ y : Fin k → Bool, (f (Fin.cons true y) - f (Fin.cons false y)) ^ 2
      = ∑ y : Fin k → Bool, (f (Fin.cons false y) - f (Fin.cons true y)) ^ 2 :=
    Finset.sum_congr rfl fun y _ => by ring
  rw [dirichlet, sum_cube_succ (fun x => ∑ i : Fin (k + 1), (f x - f (flipAt i x)) ^ 2)]
  simp only [key, Bool.not_false, Bool.not_true]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hswap, dirichlet, dirichlet]
  ring

/-! ## The Poincaré inequality for the hypercube -/

