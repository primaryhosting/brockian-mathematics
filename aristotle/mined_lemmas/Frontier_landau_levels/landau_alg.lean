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

namespace Frontier

open Polynomial

/-! ## Physicists' Hermite polynomials -/

/-- The physicists' Hermite polynomials, defined by `H₀ = 1` and
`H_{n+1} = 2X H_n - H_n'`. -/

theorem landau_alg (M H Q C F E N K Y : ℂ) (hM : M ≠ 0) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hC : C ^ 2 = Q / H) :
    1 / (2 * M) * (-H ^ 2 * (E * (C * (C * (((C * (Y - H * K / Q)) ^ 2 - (2 * N + 1)) * F))))
        + E * ((H * K - Q * Y) * ((H * K - Q * Y) * F)))
      = H * (Q / M) * (N + 1 / 2) * (E * F) := by
  have hQ' : Q = C ^ 2 * H := by field_simp at hC; linear_combination -hC
  have hC0 : C ≠ 0 := by
    intro h; apply hQ; rw [hQ', h]; ring
  subst hQ'
  field_simp
  ring

/-- **Landau levels.** For a charged particle of mass `m` and charge `q` moving in a plane
perpendicular to a uniform magnetic field `B`, the states `landauPsi` are eigenstates of the
Hamiltonian with energies `ℏ ω_c (n + 1/2)`, `ω_c = qB/m` the cyclotron frequency. -/
