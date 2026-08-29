/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.CodeToolkit

/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Summary

We work in Mathlib's standard model of computation: programs are
`Nat.Partrec.Code`s, and the running time of a program `c` on an input `n` is
`CS.time c n`, the least step bound `k` for which Mathlib's step-indexed
interpreter `Nat.Partrec.Code.evaln k c n` returns a value.  (This is a Blum
complexity measure: it is defined exactly when `c.eval n` converges, and the
predicate `time c n ≤ k` is decidable.)

The main theorem `CS.blum_speedup` says: for every computable, monotone
"speed-up factor" `T` there is a computable function `f` such that **no**
program for `f` is optimal — given any program `c` computing `f` one can
produce another program `c'` computing the *same* function `f` which, on
infinitely many inputs, is faster than `c` by more than the factor `T`:
`T (time c' n) < time c n`.

The corollary `CS.no_fastest_algorithm` states the headline consequence: the
problem `f` has no fastest algorithm, not even in the "almost everywhere"
sense.

## Relation to Blum's original theorem

Blum's speed-up theorem produces speed-ups that hold for *almost every* input.
The theorem proved here gives speed-ups on an *infinite* set of inputs (an
entire column `{Nat.pair e j | j}`, where `e` is the index of the program being
sped up).  This is weaker than the almost-everywhere form, but it is already
enough for the headline statement "there are problems with no fastest
algorithm": an almost-everywhere optimal program would in particular be at
least as fast as every competitor on all but finitely many inputs, which
`CS.no_fastest_algorithm` refutes.

The construction is a direct diagonalisation.  `diagF T n` simulates the
program coded by `n.unpair.1` on the input `n` for `bnd T n` steps and outputs
something different if that simulation converges.  Hence a program `c`
computing `diagF T` must take more than `bnd T n` steps on every input of its
own column, and on that column `diagF T` is identically `0`.  The competitor
`patch c (encode c)` answers `0` on that column (using an explicitly built
equality test whose running time is polynomially bounded) and defers to `c`
everywhere else.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ### Running time of a program -/

/-- The running time of the program `c` on input `n`: the least step bound
under which Mathlib's step-indexed interpreter produces an output.  (It is `0`
when the computation diverges.) -/
noncomputable def time (c : Code) (n : ℕ) : ℕ := sInf {k | (evaln k c n).isSome}

/-- `c` computes the total function `f`. -/
def Computes (c : Code) (f : ℕ → ℕ) : Prop := ∀ n, c.eval n = Part.some (f n)

theorem time_le_of_evaln {c : Code} {n k : ℕ} (h : (evaln k c n).isSome) : time c n ≤ k :=
  Nat.sInf_le h

theorem evaln_isSome_of_time_le {c : Code} {n k : ℕ} (hc : (c.eval n).Dom)
    (h : time c n ≤ k) : (evaln k c n).isSome := by
  obtain ⟨k₀, hk₀⟩ := evaln_complete.1 (Part.get_mem hc)
  have hk₀' : evaln k₀ c n = some ((c.eval n).get hc) := hk₀
  have hne : {k | (evaln k c n).isSome}.Nonempty := ⟨k₀, by simp [Set.mem_setOf_eq, hk₀']⟩
  have hmem : (evaln (time c n) c n).isSome := Nat.sInf_mem hne
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hmem
  have hv' : v ∈ evaln (time c n) c n := hv
  have hmono := evaln_mono (k₁ := time c n) (k₂ := k) h hv'
  have : evaln k c n = some v := hmono
  simp [this]

theorem lt_time_of_evaln_none {c : Code} {n k : ℕ} (hc : (c.eval n).Dom)
    (h : evaln k c n = Option.none) : k < time c n := by
  by_contra hcon
  have := evaln_isSome_of_time_le hc (Nat.le_of_not_lt hcon)
  simp [h] at this

/-! ### A branching combinator for codes -/

/-- `branch A B t` computes `if t n = 0 then A n else B n`, assuming `t n ≤ 1`. -/
def branch (A B t : Code) : Code := comp (prec A (comp B left)) (pair Code.id t)

theorem evaln_branch_zero {A B t : Code} {k n v : ℕ} (hn : n ≤ k) (hp : Nat.pair n 0 ≤ k)
    (ht : evaln (k + 1) t n = some 0) (hA : evaln (k + 1) A n = some v) :
    evaln (k + 1) (branch A B t) n = some v := by
  have hq : evaln (k + 1) (pair Code.id t) n = some (Nat.pair n 0) :=
    evaln_pair' hn (evaln_id' hn) ht
  exact evaln_comp' hn hq (evaln_prec_zero' hp hA)

theorem evaln_branch_one {A B t : Code} {k' n v w : ℕ} (hn : n ≤ k' + 1)
    (hp1 : Nat.pair n 1 ≤ k' + 1) (hp0 : Nat.pair n 0 ≤ k')
    (hz : Nat.pair n (Nat.pair 0 w) ≤ k' + 1)
    (ht : evaln (k' + 2) t n = some 1) (hA : evaln (k' + 1) A n = some w)
    (hB : evaln (k' + 2) B n = some v) :
    evaln (k' + 2) (branch A B t) n = some v := by
  have hq : evaln (k' + 2) (pair Code.id t) n = some (Nat.pair n 1) :=
    evaln_pair' hn (evaln_id' hn) ht
  have hrec : evaln (k' + 1) (prec A (comp B left)) (Nat.pair n 0) = some w :=
    evaln_prec_zero' hp0 hA
  have hleft : evaln (k' + 2) left (Nat.pair n (Nat.pair 0 w)) = some n := by
    have := evaln_left' (k := k' + 1) (n := Nat.pair n (Nat.pair 0 w)) hz
    simpa using this
  have hg : evaln (k' + 2) (comp B left) (Nat.pair n (Nat.pair 0 w)) = some v :=
    evaln_comp' hz hleft hB
  exact evaln_comp' hn hq (evaln_prec_succ' hp1 hrec hg)

/-! ### The patched program -/

/-- `eqLE e` computes `min (n.unpair.1 - e) 1`; it is `0` exactly when `n.unpair.1 ≤ e`. -/
def eqLE (e : ℕ) : Code := comp sgC (comp subC (pair left (Code.const e)))

/-- `eqGE e` computes `min (e - n.unpair.1) 1`; it is `0` exactly when `e ≤ n.unpair.1`. -/
def eqGE (e : ℕ) : Code := comp sgC (comp subC (pair (Code.const e) left))

/-- `patch c e` computes `if n.unpair.1 = e then 0 else c n`. -/
def patch (c : Code) (e : ℕ) : Code := branch (branch zero c (eqGE e)) c (eqLE e)

theorem evaln_eqLE {N e n k : ℕ} (he : e ≤ N) (hn : n ≤ N) (h : (2 * N + 2) ^ 4 + 2 * N ≤ k) :
    evaln (k + 1) (eqLE e) n = some (min (n.unpair.1 - e) 1) := by
  have hq := self_le_quart N
  have ha : n.unpair.1 ≤ N := le_trans (Nat.unpair_left_le n) hn
  have h1 : evaln (k + 1) (pair left (Code.const e)) n = some (Nat.pair n.unpair.1 e) :=
    evaln_pair' (by omega) (evaln_left' (by omega)) (evaln_const' (by omega) (by omega))
  have h2 : evaln (k + 1) subC (Nat.pair n.unpair.1 e) = some (n.unpair.1 - e) :=
    evaln_subC (N := N) ha he (by omega)
  have h3 : evaln (k + 1) sgC (n.unpair.1 - e) = some (min (n.unpair.1 - e) 1) :=
    evaln_sgC (N := N) (by omega) (by omega)
  exact evaln_comp' (by omega) (evaln_comp' (by omega) h1 h2) h3

theorem evaln_eqGE {N e n k : ℕ} (he : e ≤ N) (hn : n ≤ N) (h : (2 * N + 2) ^ 4 + 2 * N ≤ k) :
    evaln (k + 1) (eqGE e) n = some (min (e - n.unpair.1) 1) := by
  have hq := self_le_quart N
  have ha : n.unpair.1 ≤ N := le_trans (Nat.unpair_left_le n) hn
  have h1 : evaln (k + 1) (pair (Code.const e) left) n = some (Nat.pair e n.unpair.1) :=
    evaln_pair' (by omega) (evaln_const' (by omega) (by omega)) (evaln_left' (by omega))
  have h2 : evaln (k + 1) subC (Nat.pair e n.unpair.1) = some (e - n.unpair.1) :=
    evaln_subC (N := N) he ha (by omega)
  have h3 : evaln (k + 1) sgC (e - n.unpair.1) = some (min (e - n.unpair.1) 1) :=
    evaln_sgC (N := N) (by omega) (by omega)
  exact evaln_comp' (by omega) (evaln_comp' (by omega) h1 h2) h3

theorem evaln_patch_eq {c : Code} {N e n k : ℕ} (he : e ≤ N) (hn : n ≤ N)
    (hae : n.unpair.1 = e) (hk : (2 * N + 2) ^ 4 + 2 * N ≤ k) :
    evaln (k + 1) (patch c e) n = some 0 := by
  have hq := self_le_quart N
  have hpn0 : Nat.pair n 0 ≤ (2 * N + 2) ^ 4 := pair_le_quart hn (Nat.zero_le _)
  have hLE : evaln (k + 1) (eqLE e) n = some 0 := by
    have := evaln_eqLE (N := N) he hn hk
    simpa [hae] using this
  have hGE : evaln (k + 1) (eqGE e) n = some 0 := by
    have := evaln_eqGE (N := N) he hn hk
    simpa [hae] using this
  have hinner : evaln (k + 1) (branch zero c (eqGE e)) n = some 0 :=
    evaln_branch_zero (by omega) (by omega) hGE (evaln_zero' (by omega))
  exact evaln_branch_zero (by omega) (by omega) hLE hinner

theorem evaln_patch_ne {c : Code} {N e n k v : ℕ} (he : e ≤ N) (hn : n ≤ N)
    (hae : n.unpair.1 ≠ e) (hk : (2 * N + 2) ^ 4 + 2 * N + 2 ≤ k)
    (hc : evaln (k + 1) c n = some v) :
    evaln (k + 1) (patch c e) n = some v := by
  have hq := self_le_quart N
  have hpn0 : Nat.pair n 0 ≤ (2 * N + 2) ^ 4 := pair_le_quart hn (Nat.zero_le _)
  have hpn1 : Nat.pair n 1 ≤ (2 * N + 2) ^ 4 :=
    le_trans (pair_le n 1)
      (le_trans (Nat.pow_le_pow_left (by omega) 2) (Nat.pow_le_pow_right (by omega) (by omega)))
  have hz : Nat.pair n (Nat.pair 0 0) ≤ (2 * N + 2) ^ 4 := by
    have h00 : Nat.pair 0 0 = 0 := by norm_num [Nat.pair]
    rw [h00]; exact hpn0
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rcases lt_or_gt_of_ne hae with hlt | hgt
  · -- `n.unpair.1 < e` : the outer test is `0`, the inner test is `1`
    have hLE : evaln (k' + 1 + 1) (eqLE e) n = some 0 := by
      have := evaln_eqLE (N := N) he hn (k := k' + 1) (by omega)
      have h0 : min (n.unpair.1 - e) 1 = 0 := by omega
      rw [h0] at this; exact this
    have hGE : evaln (k' + 1 + 1) (eqGE e) n = some 1 := by
      have := evaln_eqGE (N := N) he hn (k := k' + 1) (by omega)
      have h0 : min (e - n.unpair.1) 1 = 1 := by omega
      rw [h0] at this; exact this
    have hinner : evaln (k' + 2) (branch zero c (eqGE e)) n = some v :=
      evaln_branch_one (w := 0) (by omega) (by omega) (by omega) (le_trans hz (by omega))
        hGE (evaln_zero' (by omega)) hc
    exact evaln_branch_zero (by omega) (by omega) hLE hinner
  · -- `e < n.unpair.1` : the outer test is `1`
    have hLE : evaln (k' + 1 + 1) (eqLE e) n = some 1 := by
      have := evaln_eqLE (N := N) he hn (k := k' + 1) (by omega)
      have h0 : min (n.unpair.1 - e) 1 = 1 := by omega
      rw [h0] at this; exact this
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    have hGE : evaln (k'' + 1 + 1) (eqGE e) n = some 0 := by
      have := evaln_eqGE (N := N) he hn (k := k'' + 1) (by omega)
      have h0 : min (e - n.unpair.1) 1 = 0 := by omega
      rw [h0] at this; exact this
    have hinner : evaln (k'' + 1 + 1) (branch zero c (eqGE e)) n = some 0 :=
      evaln_branch_zero (by omega) (by omega) hGE (evaln_zero' (by omega))
    exact evaln_branch_one (w := 0) (by omega) (by omega) (by omega) (le_trans hz (by omega))
      hLE hinner hc

/-! ### The diagonal function -/

/-- The step budget used by the diagonalisation. -/
def big (n : ℕ) : ℕ := (2 * n + 2) ^ 4 + 2 * n + 3

/-- The simulation bound: any program which is faster than this on its own
column gets diagonalised against. -/
def bnd (T : ℕ → ℕ) (n : ℕ) : ℕ := T (big n) + big n

/-- The hard function: on input `n`, simulate the program coded by `n.unpair.1`
for `bnd T n` steps and output something different if it converges. -/
def diagF (T : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((evaln (bnd T n) (Denumerable.ofNat Code n.unpair.1) n).map (· + 1)).getD 0

theorem primrec_big : Primrec big := by
  have h1 : Primrec fun n : ℕ => 2 * n + 2 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 2)
  have h2 : Primrec fun n : ℕ => (2 * n + 2) * (2 * n + 2) := Primrec.nat_mul.comp h1 h1
  have h3 : Primrec fun n : ℕ => (2 * n + 2) ^ 4 := by
    have h4 : (fun n : ℕ => (2 * n + 2) ^ 4)
        = fun n => ((2 * n + 2) * (2 * n + 2)) * ((2 * n + 2) * (2 * n + 2)) := by
      funext n; ring
    rw [h4]; exact Primrec.nat_mul.comp h2 h2
  exact Primrec.nat_add.comp (Primrec.nat_add.comp h3
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)) (Primrec.const 3)

theorem computable_diagF {T : ℕ → ℕ} (hT : Computable T) : Computable (diagF T) := by
  have hbig : Computable big := primrec_big.to_comp
  have hbnd : Computable (bnd T) := Primrec.nat_add.to_comp.comp (hT.comp hbig) hbig
  have hcode : Computable fun n : ℕ => Denumerable.ofNat Code n.unpair.1 :=
    ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.unpair)).to_comp
  have hev : Computable fun n : ℕ => evaln (bnd T n) (Denumerable.ofNat Code n.unpair.1) n :=
    (Nat.Partrec.Code.primrec_evaln.to_comp).comp
      (Computable.pair (Computable.pair hbnd hcode) Computable.id)
  exact Computable.option_getD
    (Computable.option_map hev (Computable.succ.comp Computable.snd).to₂) (Computable.const 0)

/-! ### The diagonalisation is successful on the column of each program for `diagF T` -/

/-- If `c` computes `diagF T` then on its own column `c` cannot converge within
`bnd T n` steps, and consequently `diagF T` vanishes there. -/
theorem diag_col {T : ℕ → ℕ} {c : Code} (hc : Computes c (diagF T)) {n : ℕ}
    (hn : n.unpair.1 = Encodable.encode c) :
    evaln (bnd T n) c n = Option.none ∧ diagF T n = 0 := by
  have hdec : Denumerable.ofNat Code n.unpair.1 = c := by
    rw [hn]; exact Denumerable.ofNat_encode c
  cases hev : evaln (bnd T n) c n with
  | none => exact ⟨rfl, by simp [diagF, hdec, hev]⟩
  | some v =>
      exfalso
      have hmem : v ∈ c.eval n := evaln_sound (k := bnd T n) (by simp [hev])
      rw [hc n] at hmem
      have hv : v = diagF T n := Part.mem_some_iff.1 hmem
      have hdiag : diagF T n = v + 1 := by simp [diagF, hdec, hev]
      omega

/-! ### The main theorem -/

/-- The patched program computes the same function as the original one. -/
theorem patch_computes {T : ℕ → ℕ} {c : Code} (hc : Computes c (diagF T)) :
    Computes (patch c (Encodable.encode c)) (diagF T) := by
  intro n
  by_cases hcol : n.unpair.1 = Encodable.encode c
  · have hzero := (diag_col hc hcol).2
    have hen : Encodable.encode c ≤ n := by rw [← hcol]; exact Nat.unpair_left_le n
    have hev : evaln ((2 * n + 2) ^ 4 + 2 * n + 1) (patch c (Encodable.encode c)) n = some 0 :=
      evaln_patch_eq (N := n) hen le_rfl hcol le_rfl
    have hmem : (0 : ℕ) ∈ (patch c (Encodable.encode c)).eval n :=
      evaln_sound (k := (2 * n + 2) ^ 4 + 2 * n + 1) (by simp [hev])
    rw [hzero]
    exact Part.eq_some_iff.2 hmem
  · have hmem : diagF T n ∈ c.eval n := by rw [hc n]; exact Part.mem_some _
    obtain ⟨k₁, hk₁⟩ := evaln_complete.1 hmem
    set N := max (Encodable.encode c) n with hN
    set k := max k₁ ((2 * N + 2) ^ 4 + 2 * N + 2) with hk
    have hck : evaln (k + 1) c n = some (diagF T n) :=
      evaln_mono (le_trans (le_max_left _ _) (Nat.le_succ k)) hk₁
    have hpatch : evaln (k + 1) (patch c (Encodable.encode c)) n = some (diagF T n) :=
      evaln_patch_ne (N := N) (le_max_left _ _) (le_max_right _ _) hcol (le_max_right _ _) hck
    exact Part.eq_some_iff.2 (evaln_sound (k := k + 1) (by simp [hpatch]))

/-- **Blum's speed-up theorem** (infinitely-often form).

For every computable, monotone "speed-up factor" `T` there is a computable
function `f` with the following property: for *every* program `c` computing
`f` there is another program `c'` computing the very same function `f` which,
on infinitely many inputs, beats `c` by more than the factor `T`, i.e.
`T (time c' n) < time c n`.  In particular the problem `f` has no fastest
algorithm. -/
theorem blum_speedup (T : ℕ → ℕ) (hT : Computable T) (hTmono : Monotone T) :
    ∃ f : ℕ → ℕ, Computable f ∧
      ∀ c : Code, Computes c f →
        ∃ c' : Code, Computes c' f ∧ {n | T (time c' n) < time c n}.Infinite := by
  refine ⟨diagF T, computable_diagF hT, ?_⟩
  intro c hc
  refine ⟨patch c (Encodable.encode c), patch_computes hc, ?_⟩
  refine Set.infinite_of_injective_forall_mem
    (f := fun j : ℕ => Nat.pair (Encodable.encode c) j) ?_ ?_
  · intro j₁ j₂ h
    simpa using congrArg (fun x => x.unpair.2) h
  · intro j
    have hcol : (Nat.pair (Encodable.encode c) j).unpair.1 = Encodable.encode c := by simp
    set n := Nat.pair (Encodable.encode c) j with hn
    have hen : Encodable.encode c ≤ n := by rw [← hcol]; exact Nat.unpair_left_le n
    obtain ⟨hnone, hzero⟩ := diag_col hc hcol
    have hdom : (c.eval n).Dom := by rw [hc n]; trivial
    have hslow : bnd T n < time c n := lt_time_of_evaln_none hdom hnone
    have hfast : time (patch c (Encodable.encode c)) n ≤ big n := by
      have hev : evaln ((2 * n + 2) ^ 4 + 2 * n + 1) (patch c (Encodable.encode c)) n = some 0 :=
        evaln_patch_eq (N := n) hen le_rfl hcol le_rfl
      have hle : time (patch c (Encodable.encode c)) n ≤ (2 * n + 2) ^ 4 + 2 * n + 1 :=
        time_le_of_evaln (by simp [hev])
      unfold big; omega
    have h1 : T (time (patch c (Encodable.encode c)) n) ≤ T (big n) := hTmono hfast
    have h2 : T (big n) ≤ bnd T n := by unfold bnd; omega
    show T (time (patch c (Encodable.encode c)) n) < time c n
    omega

/-- **There are problems with no fastest algorithm.**

There is a computable function `f` (so the problem *is* solvable
algorithmically) such that no program computing `f` is optimal, not even
almost everywhere: for every program `c` for `f` there is a program `c'` for
`f` which is strictly faster than `c` on infinitely many inputs. -/
theorem no_fastest_algorithm :
    ∃ f : ℕ → ℕ, Computable f ∧ (∃ c : Code, Computes c f) ∧
      ∀ c : Code, Computes c f →
        ¬ ∀ c' : Code, Computes c' f → ∀ᶠ n in Filter.atTop, time c n ≤ time c' n := by
  obtain ⟨f, hf, hspeed⟩ := blum_speedup id Computable.id monotone_id
  refine ⟨f, hf, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hf.partrec)
    exact ⟨c, fun n => by rw [hc]; rfl⟩
  · intro c hc hopt
    obtain ⟨c', hc', hinf⟩ := hspeed c hc
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hopt c' hc')
    obtain ⟨n, hn, hlt⟩ := hinf.exists_gt N
    have h1 : time c n ≤ time c' n := hN n (le_of_lt hlt)
    have h2 : time c' n < time c n := hn
    omega

end CS

import Mathlib

/-!
# A toolkit for step-bounded evaluation of partial recursive codes

This file develops explicit `Nat.Partrec.Code` programs for a few arithmetic
operations (predecessor, truncated subtraction, addition, the sign function)
together with *explicit bounds on the number of steps* that Mathlib's
step-indexed evaluator `Nat.Partrec.Code.evaln` needs in order to produce their
values.

These bounds are what makes it possible to talk about the *running time* of a
program, the notion used in `RequestProject.BlumSpeedup`.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ### Elementary bounds on Cantor pairing -/

theorem pair_le (a b : ℕ) : Nat.pair a b ≤ (a + b + 1) ^ 2 := by
  rw [Nat.pair]; split <;> nlinarith [sq_nonneg (a + b)]

theorem pair_le_sq {a b N : ℕ} (ha : a ≤ N) (hb : b ≤ N) : Nat.pair a b ≤ (2 * N + 1) ^ 2 :=
  le_trans (pair_le a b) (Nat.pow_le_pow_left (by omega) 2)

theorem sq_le_quart (N : ℕ) : (2 * N + 1) ^ 2 ≤ (2 * N + 2) ^ 4 := by
  calc (2 * N + 1) ^ 2 ≤ (2 * N + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ ≤ (2 * N + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)

theorem pair_nest_le {a c N : ℕ} (ha : a ≤ N) (hc : c ≤ (2 * N + 1) ^ 2) :
    Nat.pair a c ≤ (2 * N + 2) ^ 4 := by
  calc Nat.pair a c ≤ (a + c + 1) ^ 2 := pair_le _ _
    _ ≤ (N + (2 * N + 1) ^ 2 + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ ≤ ((2 * N + 2) ^ 2) ^ 2 := Nat.pow_le_pow_left (by nlinarith) 2
    _ = (2 * N + 2) ^ 4 := by ring

theorem pair_le_quart {a b N : ℕ} (ha : a ≤ N) (hb : b ≤ N) :
    Nat.pair a b ≤ (2 * N + 2) ^ 4 :=
  le_trans (pair_le_sq ha hb) (sq_le_quart N)

theorem self_le_quart (N : ℕ) : N ≤ (2 * N + 2) ^ 4 := by
  calc N ≤ 2 * N + 2 := by omega
    _ ≤ (2 * N + 2) ^ 4 := Nat.le_self_pow (by norm_num) _

/-! ### Basic step-bounded evaluation lemmas -/

theorem evaln_zero' {k n : ℕ} (h : n ≤ k) : evaln (k + 1) zero n = some 0 := by
  simp [evaln, h]

theorem evaln_succ' {k n : ℕ} (h : n ≤ k) : evaln (k + 1) succ n = some (n + 1) := by
  simp [evaln, h]

theorem evaln_left' {k n : ℕ} (h : n ≤ k) : evaln (k + 1) left n = some n.unpair.1 := by
  simp [evaln, h]

theorem evaln_right' {k n : ℕ} (h : n ≤ k) : evaln (k + 1) right n = some n.unpair.2 := by
  simp [evaln, h]

theorem evaln_pair' {k n x y : ℕ} {cf cg : Code} (h : n ≤ k)
    (hf : evaln (k + 1) cf n = some x) (hg : evaln (k + 1) cg n = some y) :
    evaln (k + 1) (pair cf cg) n = some (Nat.pair x y) := by
  simp [evaln, h, hf, hg, Seq.seq]

theorem evaln_comp' {k n x y : ℕ} {cf cg : Code} (h : n ≤ k)
    (hg : evaln (k + 1) cg n = some x) (hf : evaln (k + 1) cf x = some y) :
    evaln (k + 1) (comp cf cg) n = some y := by
  simp [evaln, h, hg, hf]

theorem evaln_prec_zero' {k a v : ℕ} {cf cg : Code} (h : Nat.pair a 0 ≤ k)
    (hf : evaln (k + 1) cf a = some v) :
    evaln (k + 1) (prec cf cg) (Nat.pair a 0) = some v := by
  simp [evaln, h, hf]

theorem evaln_prec_succ' {k a m i v : ℕ} {cf cg : Code} (h : Nat.pair a (m + 1) ≤ k)
    (hrec : evaln k (prec cf cg) (Nat.pair a m) = some i)
    (hg : evaln (k + 1) cg (Nat.pair a (Nat.pair m i)) = some v) :
    evaln (k + 1) (prec cf cg) (Nat.pair a (m + 1)) = some v := by
  simp [evaln, h, hrec, hg]

theorem evaln_id' {k n : ℕ} (h : n ≤ k) : evaln (k + 1) Code.id n = some n := by
  have := evaln_pair' (cf := left) (cg := right) h (evaln_left' h) (evaln_right' h)
  simpa [Code.id] using this

theorem evaln_const' : ∀ {m k n : ℕ}, n ≤ k → m ≤ k →
    evaln (k + 1) (Code.const m) n = some m
  | 0, k, n, hn, _ => by simpa [Nat.Partrec.Code.const] using evaln_zero' hn
  | m + 1, k, n, hn, hm => by
      refine evaln_comp' hn (evaln_const' hn (by omega)) ?_
      exact evaln_succ' (by omega)

/-! ### The arithmetic codes -/

/-- `precZ` maps `Nat.pair 0 m` to `m - 1`. -/
def precZ : Code := prec zero (comp left right)

/-- `pred1C` computes the predecessor function `x ↦ x - 1`. -/
def pred1C : Code := comp precZ (pair zero Code.id)

/-- `subC` computes truncated subtraction: `Nat.pair a b ↦ a - b`. -/
def subC : Code := prec Code.id (comp pred1C (comp right right))

/-- `sgC` computes `x ↦ min x 1`. -/
def sgC : Code := comp subC (pair Code.id pred1C)

theorem evaln_precZ : ∀ {N m k : ℕ}, m ≤ N → (2 * N + 2) ^ 4 + m ≤ k →
    evaln (k + 1) precZ (Nat.pair 0 m) = some (m - 1)
  | _, 0, k, _, _ => by
      refine evaln_prec_zero' (by norm_num [Nat.pair]) ?_
      exact evaln_zero' (Nat.zero_le _)
  | N, m + 1, k, hmN, h => by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hIH : evaln (k' + 1) precZ (Nat.pair 0 m) = some (m - 1) :=
        evaln_precZ (N := N) (by omega) (by omega)
      have hb1 : Nat.pair m (m - 1) ≤ (2 * N + 1) ^ 2 := pair_le_sq (by omega) (by omega)
      have hb2 : Nat.pair 0 (Nat.pair m (m - 1)) ≤ (2 * N + 2) ^ 4 :=
        pair_nest_le (Nat.zero_le _) hb1
      have hb3 : Nat.pair 0 (m + 1) ≤ (2 * N + 2) ^ 4 := pair_le_quart (Nat.zero_le _) (by omega)
      have hb4 : (2 * N + 1) ^ 2 ≤ (2 * N + 2) ^ 4 := sq_le_quart N
      refine evaln_prec_succ' (k := k' + 1) (by omega) hIH ?_
      refine evaln_comp' (by omega) (evaln_right' (by omega)) ?_
      simp only [Nat.unpair_pair]
      have h4 := evaln_left' (k := k' + 1) (n := Nat.pair m (m - 1)) (by omega)
      simpa using h4

theorem evaln_pred1C {N x k : ℕ} (hx : x ≤ N) (h : (2 * N + 2) ^ 4 + N ≤ k) :
    evaln (k + 1) pred1C x = some (x - 1) := by
  have hq := self_le_quart N
  have h1 : evaln (k + 1) (pair zero Code.id) x = some (Nat.pair 0 x) := by
    have := evaln_pair' (cf := zero) (cg := Code.id) (n := x) (k := k)
      (by omega) (evaln_zero' (by omega)) (evaln_id' (by omega))
    simpa using this
  have h2 : evaln (k + 1) precZ (Nat.pair 0 x) = some (x - 1) :=
    evaln_precZ (N := N) hx (by omega)
  exact evaln_comp' (by omega) h1 h2

theorem evaln_subC : ∀ {N a b k : ℕ}, a ≤ N → b ≤ N → (2 * N + 2) ^ 4 + N + b ≤ k →
    evaln (k + 1) subC (Nat.pair a b) = some (a - b)
  | N, a, 0, k, haN, _, h => by
      have hb : Nat.pair a 0 ≤ (2 * N + 2) ^ 4 := pair_le_quart haN (Nat.zero_le _)
      exact evaln_prec_zero' (by omega) (evaln_id' (by omega))
  | N, a, b + 1, k, haN, hbN, h => by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hIH : evaln (k' + 1) subC (Nat.pair a b) = some (a - b) :=
        evaln_subC (N := N) haN (by omega) (by omega)
      have hpmi : Nat.pair b (a - b) ≤ (2 * N + 1) ^ 2 := pair_le_sq (by omega) (by omega)
      have hz : Nat.pair a (Nat.pair b (a - b)) ≤ (2 * N + 2) ^ 4 := pair_nest_le haN hpmi
      have hab : Nat.pair a (b + 1) ≤ (2 * N + 2) ^ 4 := pair_le_quart haN hbN
      have hb4 : (2 * N + 1) ^ 2 ≤ (2 * N + 2) ^ 4 := sq_le_quart N
      refine evaln_prec_succ' (k := k' + 1) (by omega) hIH ?_
      have hr1 : evaln (k' + 1 + 1) right (Nat.pair a (Nat.pair b (a - b)))
          = some (Nat.pair b (a - b)) := by
        have := evaln_right' (k := k' + 1) (n := Nat.pair a (Nat.pair b (a - b))) (by omega)
        simpa using this
      have hr2 : evaln (k' + 1 + 1) right (Nat.pair b (a - b)) = some (a - b) := by
        have := evaln_right' (k := k' + 1) (n := Nat.pair b (a - b)) (by omega)
        simpa using this
      have hrr : evaln (k' + 1 + 1) (comp right right) (Nat.pair a (Nat.pair b (a - b)))
          = some (a - b) := evaln_comp' (by omega) hr1 hr2
      have hp : evaln (k' + 1 + 1) pred1C (a - b) = some (a - (b + 1)) := by
        have h5 : a - b - 1 = a - (b + 1) := by omega
        have := evaln_pred1C (N := N) (x := a - b) (k := k' + 1) (by omega) (by omega)
        rwa [h5] at this
      exact evaln_comp' (by omega) hrr hp

theorem evaln_sgC {N x k : ℕ} (hx : x ≤ N) (h : (2 * N + 2) ^ 4 + 2 * N ≤ k) :
    evaln (k + 1) sgC x = some (min x 1) := by
  have hq := self_le_quart N
  have hstep : evaln (k + 1) (pair Code.id pred1C) x = some (Nat.pair x (x - 1)) :=
    evaln_pair' (by omega) (evaln_id' (by omega)) (evaln_pred1C (N := N) hx (by omega))
  have hsub : evaln (k + 1) subC (Nat.pair x (x - 1)) = some (x - (x - 1)) :=
    evaln_subC (N := N) hx (by omega) (by omega)
  have hmin : x - (x - 1) = min x 1 := by omega
  rw [← hmin]
  exact evaln_comp' (by omega) hstep hsub

end CS

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

