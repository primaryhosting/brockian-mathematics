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

import RequestProject.BGS.OracleA
import RequestProject.BGS.OracleB

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Statement: There are oracles A,B with P^A=NP^A and P^B≠NP^B (relativization barrier).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header block above is placed directly after the `import` lines, because Lean 4
requires `import` commands to be the very first commands of a module.)

## Summary of the development

Everything is developed from scratch in this project:

* `CS.Stmt`, `CS.step`, `CS.run` (`RequestProject/BGS/Model.lean`): a concrete model of
  oracle computation.  Programs are statements of a small imperative language with
  string registers; oracle queries are built one symbol at a time in a dedicated query
  register, so that *the length of a query never exceeds the number of steps performed*.
* `CS.PClass`, `CS.NPClass` (`RequestProject/BGS/Classes.lean`): the relativized classes
  `P^O` and `NP^O`, defined with the polynomial bounds `pb k n = (n+2)^(k+1)`.
* `CS.A` (`RequestProject/BGS/OracleA.lean`): a self-referential oracle answering
  `NP^A`-questions in one query; well defined by recursion on the length of the queried
  string.  It satisfies `P^A = NP^A`.
* `CS.B` (`RequestProject/BGS/OracleB.lean`): an oracle built by stages, diagonalizing
  against every polynomial time oracle machine, for which the language
  `CS.Lang B = { x | ∃ u, |u| = |x| ∧ u ∈ B }` lies in `NP^B` but not in `P^B`.
-/

namespace CS

/-- **Baker–Gill–Solovay**: there is an oracle `A` with `P^A = NP^A` and an oracle `B`
with `P^B ≠ NP^B`; hence no relativizing proof can settle the `P` versus `NP` question. -/

theorem padProg_exec (O : Oracle) : ∀ (d : ℕ) (st : St),
    ∃ (c : ℕ) (st' : St), c ≤ ((st.regs 9).length + 4) ^ (d + 1) ∧ Exec O (padProg d) st st' c ∧
      st'.q = st.q ++ List.replicate ((st.regs 9).length ^ d) false ∧
      (∀ j, (j ≤ 9 ∨ 10 + d ≤ j) → st'.regs j = st.regs j) ∧ st'.log = st.log := by
  intro d
  induction d with
  | zero =>
    intro st
    refine ⟨1, { st with q := st.q ++ [false] }, ?_, Exec.pushQC O st false, ?_, ?_, rfl⟩
    · simp
    · simp
    · intro j _; rfl
  | succ d IH =>
    have loop : ∀ (ℓ : ℕ) (st : St), (st.regs (10 + d)).length = ℓ →
        ∃ (c : ℕ) (st' : St),
          c ≤ ℓ * (((st.regs 9).length + 4) ^ (d + 1) + 3) + 1 ∧
          Exec O (Stmt.whileNE (10 + d) (Stmt.seq (padProg d) (Stmt.pop (10 + d)))) st st' c ∧
          st'.q = st.q ++ List.replicate (ℓ * (st.regs 9).length ^ d) false ∧
          (∀ j, (j ≤ 9 ∨ 11 + d ≤ j) → st'.regs j = st.regs j) ∧ st'.log = st.log := by
      intro ℓ
      induction ℓ with
      | zero =>
        intro st h
        refine ⟨1, st, by omega, Exec.while_done (by simpa using h), by simp, ?_, rfl⟩
        intro j _; rfl
      | succ ℓ ihl =>
        intro st h
        have hne : st.regs (10 + d) ≠ [] := by
          intro hc; rw [hc] at h; simp at h
        obtain ⟨c₁, st₁, hc₁, hex₁, hq₁, hr₁, hl₁⟩ := IH st
        have h9 : st₁.regs 9 = st.regs 9 := hr₁ 9 (Or.inl (by omega))
        have hcnt : st₁.regs (10 + d) = st.regs (10 + d) := hr₁ (10 + d) (Or.inr (by omega))
        have hpop := Exec.pop O st₁ (10 + d)
        set st₂ : St := st₁.setReg (10 + d) (st₁.regs (10 + d)).tail with hst₂
        have hbody := Exec.seq hex₁ hpop
        have h9' : st₂.regs 9 = st.regs 9 := by
          rw [hst₂, St.setReg_ne _ (by omega), h9]
        have hcnt' : (st₂.regs (10 + d)).length = ℓ := by
          rw [hst₂, St.setReg_same, hcnt]
          rcases hx : st.regs (10 + d) with _ | ⟨a, r⟩
          · rw [hx] at h; simp at h
          · rw [hx] at h; simp at h ⊢; omega
        obtain ⟨c₂, st₃, hc₂, hex₂, hq₂, hr₂, hl₂⟩ := ihl st₂ hcnt'
        refine ⟨c₁ + 1 + 1 + c₂ + 1, st₃, ?_, Exec.while_step hne hbody hex₂, ?_, ?_, ?_⟩
        · rw [h9'] at hc₂
          have h1 : (ℓ + 1) * (((st.regs 9).length + 4) ^ (d + 1) + 3) + 1
              = ℓ * (((st.regs 9).length + 4) ^ (d + 1) + 3)
                + ((st.regs 9).length + 4) ^ (d + 1) + 4 := by ring
          rw [h1]
          linarith [hc₁, hc₂]
        · have hq3 : st₃.q = st.q ++ (List.replicate ((st.regs 9).length ^ d) false
              ++ List.replicate (ℓ * (st.regs 9).length ^ d) false) := by
            rw [hq₂, h9', hst₂]
            show st₁.q ++ _ = _
            rw [hq₁, List.append_assoc]
          have harith : (st.regs 9).length ^ d + ℓ * (st.regs 9).length ^ d
              = (ℓ + 1) * (st.regs 9).length ^ d := by ring
          rw [hq3, ← List.replicate_add, harith]
        · intro j hj
          rw [hr₂ j hj, hst₂, St.setReg_ne _ (by omega), hr₁ j (by omega)]
        · rw [hl₂, hst₂]
          show st₁.log = st.log
          exact hl₁
    intro st
    have hcopy := Exec.copy O st (10 + d) 9
    set st₀ : St := st.setReg (10 + d) (st.regs 9) with hst₀
    have h9 : st₀.regs 9 = st.regs 9 := by rw [hst₀, St.setReg_ne _ (by omega)]
    have hcnt : (st₀.regs (10 + d)).length = (st.regs 9).length := by
      rw [hst₀, St.setReg_same]
    obtain ⟨c, st', hc, hex, hq, hr, hl⟩ := loop ((st.regs 9).length) st₀ hcnt
    rw [h9] at hc hq
    refine ⟨1 + c + 1, st', ?_, Exec.seq hcopy hex, ?_, ?_, ?_⟩
    · set L := (st.regs 9).length
      set X := (L + 4) ^ (d + 1) with hX
      have hXge : L + 4 ≤ X := by
        rw [hX]
        calc L + 4 = (L + 4) ^ 1 := (pow_one _).symm
          _ ≤ (L + 4) ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hpow : ((L + 4) ^ (d + 1 + 1)) = (L + 4) * X := by
        rw [hX]; ring
      rw [hpow]
      have key : L * (X + 3) + 1 + 2 ≤ (L + 4) * X := by nlinarith
      linarith [hc]
    · rw [hq, hst₀]
      show st.q ++ _ = _
      congr 2
      rw [← pow_succ']
    · intro j hj
      rw [hr j (by omega), hst₀, St.setReg_ne _ (by omega)]
    · rw [hl, hst₀]
      rfl

/-- A sanity check on the model: the language of nonempty strings is decided in
polynomial time relative to every oracle. -/
