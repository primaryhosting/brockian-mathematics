import Mathlib
import RequestProject.Main

/-!
# A concrete model for the canonical commutation relation

This file shows that the hypotheses of `QPhys.heisenberg_uncertainty` are *consistent* with a
nonzero `ℏ`: we build the (algebraic) Fock space of finitely supported sequences `ℕ →₀ ℂ`
with the Bargmann inner product `⟪eₘ, eₙ⟫ = n! δₘₙ`, the annihilation and creation operators,
and the resulting position and momentum operators `X`, `P`, which are symmetric and satisfy
`X P - P X = i` (i.e. `ℏ = 1`).
-/

open scoped ComplexConjugate InnerProductSpace
open Finsupp

namespace QPhys

/-! ## The Bargmann inner product on `ℕ →₀ ℂ` -/

/-- The Bargmann inner product: `⟪f, g⟫ = ∑ₙ conj (f n) * g n * n!`. -/

noncomputable def fockCore : InnerProductSpace.Core ℂ (ℕ →₀ ℂ) where
  inner := fockInner
  conj_inner_symm := fockInner_conj_symm
  re_inner_nonneg := fockInner_self_nonneg
  add_left := fockInner_add_left
  smul_left := fockInner_smul_left
  definite := fockInner_definite

noncomputable instance instFockNormedAddCommGroup : NormedAddCommGroup (ℕ →₀ ℂ) :=
  fockCore.toNormedAddCommGroup

noncomputable instance instFockInnerProductSpace : InnerProductSpace ℂ (ℕ →₀ ℂ) :=
  InnerProductSpace.ofCore fockCore.toCore

