/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is a plain
-- block comment; its text is otherwise verbatim.)

import Mathlib

/-!
We work with Mathlib's model of computation `Nat.Partrec.Code` together with its canonical
step-indexed evaluator `Nat.Partrec.Code.evaln`.  The running time of a program `c` on input `x`
is the least step bound `k` for which `evaln k c x` returns a value.

We exhibit an explicit total computable function `gfun` (a doubly exponentially growing function)
with *no fastest program*: for every program `c` computing `gfun` there is another program `d`
computing `gfun` which is strictly faster on all but finitely many inputs.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ### Elementary arithmetic helpers -/

theorem two_mul_le_two_pow : ∀ m : ℕ, 4 ≤ m → 2 * m ≤ 2 ^ m := by
  intro m hm
  induction m with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> simp_all
    · have h1 := ih (by omega)
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      omega

theorem quartic_le_two_pow : ∀ t : ℕ, 20 ≤ t → (t + 2) ^ 4 + t + 4 ≤ 2 ^ t := by
  intro t ht
  induction t with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 20 with h | h
    · have hn : n = 19 := by omega
      subst hn; norm_num
    · have h1 := ih (by omega)
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      have h4 : n ^ 4 = n * (n * n * n) := by ring
      have h5 : 20 * (n * n * n) ≤ n * (n * n * n) := Nat.mul_le_mul_right _ h
      have h3 : (n + 3) ^ 4 + n + 5 ≤ 2 * ((n + 2) ^ 4 + n + 4) := by nlinarith [h5, h]
      show (n + 3) ^ 4 + (n + 1) + 4 ≤ 2 ^ (n + 1)
      omega

theorem sq_le_pair (a b : ℕ) : b * b ≤ Nat.pair a b := by
  rw [Nat.pair]; split <;> nlinarith

theorem left_le_pair (a b : ℕ) : a ≤ Nat.pair a b := by
  rw [Nat.pair]; split <;> nlinarith

theorem pair_lt_sq (a b : ℕ) : Nat.pair a b < (max a b + 1) ^ 2 := by
  rw [Nat.pair]; split <;> rcases le_total a b with h | h <;> simp [h] <;> nlinarith

/-! ### The hard problem -/

/-- The function whose computation admits no fastest program. -/
def gfun : ℕ → ℕ
  | 0 => 1
  | (x + 1) => Nat.pair (x + 1) (gfun x)

theorem gfun_eq_pair (x : ℕ) : gfun x = Nat.pair x (gfun (x - 1)) := by
  cases x with
  | zero => decide
  | succ n => simp [gfun]

theorem one_le_gfun (x : ℕ) : 1 ≤ gfun x := by
  cases x with
  | zero => simp [gfun]
  | succ n =>
    have := left_le_pair (n + 1) (gfun n)
    simp only [gfun]; omega

theorem self_le_gfun (x : ℕ) : x ≤ gfun x := by
  cases x with
  | zero => simp
  | succ n => simpa [gfun] using left_le_pair (n + 1) (gfun n)

theorem gfun_le_succ (x : ℕ) : gfun x ≤ gfun (x + 1) := by
  have h1 := sq_le_pair (x + 1) (gfun x)
  have h2 := one_le_gfun x
  have h3 : gfun x ≤ gfun x * gfun x := Nat.le_mul_of_pos_left _ h2
  simp only [gfun] at *
  omega

theorem gfun_mono : Monotone gfun := monotone_nat_of_le_succ gfun_le_succ

theorem tower_le_gfun (x : ℕ) : 2 ^ 2 ^ x ≤ gfun (x + 1) := by
  induction x with
  | zero => decide
  | succ n ih =>
    have h1 := sq_le_pair (n + 2) (gfun (n + 1))
    have h2 : 2 ^ 2 ^ (n + 1) = (2 ^ 2 ^ n) * (2 ^ 2 ^ n) := by rw [← pow_add]; ring_nf
    calc 2 ^ 2 ^ (n + 1) = (2 ^ 2 ^ n) * (2 ^ 2 ^ n) := h2
      _ ≤ gfun (n + 1) * gfun (n + 1) := Nat.mul_le_mul ih ih
      _ ≤ Nat.pair (n + 2) (gfun (n + 1)) := h1
      _ = gfun (n + 2) := by simp [gfun]

theorem gfun_le_tower (y : ℕ) : gfun y + 3 ≤ 2 ^ 2 ^ (y + 2) := by
  induction y with
  | zero => decide
  | succ n ih =>
    set A := 2 ^ 2 ^ (n + 2) with hA
    have hA2 : 2 ≤ A := by
      have h : (2:ℕ) ^ 1 ≤ 2 ^ 2 ^ (n + 2) :=
        Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
      simpa using h
    have h1 : Nat.pair (n + 1) (gfun n) < (max (n + 1) (gfun n) + 1) ^ 2 := pair_lt_sq _ _
    have h2 : max (n + 1) (gfun n) ≤ gfun n + 1 := by
      have := self_le_gfun n; omega
    have h3 : Nat.pair (n + 1) (gfun n) < (gfun n + 2) ^ 2 :=
      lt_of_lt_of_le h1 (Nat.pow_le_pow_left (by omega) 2)
    have h4 : (gfun n + 2) ^ 2 ≤ (A - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h5 : 2 ^ 2 ^ (n + 3) = A * A := by rw [hA, ← pow_add]; ring_nf
    have h6 : (A - 1) ^ 2 + 2 ≤ A * A := by
      have h' : (A - 1) ^ 2 = (A - 1) * (A - 1) := by ring
      have h'' : A - 1 + 1 = A := by omega
      nlinarith [hA2, h'']
    have h7 : gfun (n + 1) + 3 ≤ A * A := by simp only [gfun]; omega
    rw [show n + 1 + 2 = n + 3 from rfl, h5]; exact h7

/-! ### Unfolding lemmas for `evaln` -/

theorem evaln_zero' {k n : ℕ} (h : n ≤ k) : evaln (k + 1) Code.zero n = some 0 := by
  simp [evaln, h]

theorem evaln_succ' {k n : ℕ} (h : n ≤ k) : evaln (k + 1) Code.succ n = some (n + 1) := by
  simp [evaln, h]

theorem evaln_left' {k n : ℕ} (h : n ≤ k) : evaln (k + 1) Code.left n = some n.unpair.1 := by
  simp [evaln, h]

theorem evaln_right' {k n : ℕ} (h : n ≤ k) : evaln (k + 1) Code.right n = some n.unpair.2 := by
  simp [evaln, h]

theorem evaln_pair' {k n : ℕ} {cf cg : Code} (h : n ≤ k) :
    evaln (k + 1) (Code.pair cf cg) n =
      (Nat.pair <$> evaln (k + 1) cf n <*> evaln (k + 1) cg n) := by
  simp [evaln, h]

theorem evaln_comp' {k n : ℕ} {cf cg : Code} (h : n ≤ k) :
    evaln (k + 1) (Code.comp cf cg) n =
      ((evaln (k + 1) cg n).bind fun x => evaln (k + 1) cf x) := by
  simp [evaln, h]

theorem evaln_prec_zero' {k a : ℕ} {cf cg : Code} (h : Nat.pair a 0 ≤ k) :
    evaln (k + 1) (Code.prec cf cg) (Nat.pair a 0) = evaln (k + 1) cf a := by
  simp [evaln, h]

theorem evaln_prec_succ' {k a y : ℕ} {cf cg : Code} (h : Nat.pair a (y + 1) ≤ k) :
    evaln (k + 1) (Code.prec cf cg) (Nat.pair a (y + 1)) =
      (evaln k (Code.prec cf cg) (Nat.pair a y)).bind fun i =>
        evaln (k + 1) cg (Nat.pair a (Nat.pair y i)) := by
  simp [evaln, h]

/-! ### An a priori bound on the size of outputs -/

/-- Structural depth of a code; it controls how much a program can blow up the size of its
output relative to its running time. -/
def cdepth : Code → ℕ
  | Code.zero => 1
  | Code.succ => 1
  | Code.left => 1
  | Code.right => 1
  | Code.pair cf cg => 1 + max (cdepth cf) (cdepth cg)
  | Code.comp cf cg => 1 + max (cdepth cf) (cdepth cg)
  | Code.prec cf cg => 1 + max (cdepth cf) (cdepth cg)
  | Code.rfind' cf => 1 + cdepth cf

private theorem pow_pow_mono (k : ℕ) {d e : ℕ} (h : d ≤ e) :
    (k + 3) ^ 2 ^ d ≤ (k + 3) ^ 2 ^ e :=
  Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by norm_num) h)

private theorem base_le_pow_pow (k d : ℕ) : k + 3 ≤ (k + 3) ^ 2 ^ d :=
  Nat.le_self_pow (by positivity) _

private theorem pow_pow_succ (k d : ℕ) :
    (k + 3) ^ 2 ^ (1 + d) = ((k + 3) ^ 2 ^ d) * ((k + 3) ^ 2 ^ d) := by
  rw [Nat.add_comm 1 d, pow_succ, pow_mul]; ring

/-- A program running for `k` steps can only produce outputs of size at most
`(k+2) ^ 2 ^ (depth)`. -/
theorem evaln_output_bound :
    ∀ (k : ℕ) (c : Code) (n m : ℕ), evaln k c n = some m → m + 2 ≤ (k + 2) ^ 2 ^ cdepth c := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  match k with
  | 0 => intro c n m h; simp [evaln] at h
  | (k + 1) =>
    intro c
    induction c with
    | zero =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff] at h
      show m + 2 ≤ (k + 3) ^ (2 ^ 1)
      have h' : (k + 3) ^ (2 ^ 1) = (k + 3) * (k + 3) := by norm_num [pow_succ]
      rw [h']; nlinarith [h.2]
    | succ =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff] at h
      show m + 2 ≤ (k + 3) ^ (2 ^ 1)
      have h' : (k + 3) ^ (2 ^ 1) = (k + 3) * (k + 3) := by norm_num [pow_succ]
      rw [h']; nlinarith [h.1, h.2]
    | left =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff] at h
      have h1 : m ≤ n := by rw [← h.2]; exact Nat.unpair_left_le n
      show m + 2 ≤ (k + 3) ^ (2 ^ 1)
      have h' : (k + 3) ^ (2 ^ 1) = (k + 3) * (k + 3) := by norm_num [pow_succ]
      rw [h']; nlinarith [h.1]
    | right =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff] at h
      have h1 : m ≤ n := by rw [← h.2]; exact Nat.unpair_right_le n
      show m + 2 ≤ (k + 3) ^ (2 ^ 1)
      have h' : (k + 3) ^ (2 ^ 1) = (k + 3) * (k + 3) := by norm_num [pow_succ]
      rw [h']; nlinarith [h.1]
    | pair cf cg ihf ihg =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff, Seq.seq] at h
      obtain ⟨hn, a, ha, b, hb, hab⟩ := h
      have h1 : a + 2 ≤ (k + 3) ^ 2 ^ cdepth cf := ihf n a ha
      have h2 : b + 2 ≤ (k + 3) ^ 2 ^ cdepth cg := ihg n b hb
      show m + 2 ≤ (k + 3) ^ 2 ^ (1 + max (cdepth cf) (cdepth cg))
      rw [pow_pow_succ]
      set C := (k + 3) ^ 2 ^ (max (cdepth cf) (cdepth cg)) with hC
      have hf : (k + 3) ^ 2 ^ cdepth cf ≤ C := pow_pow_mono k (le_max_left _ _)
      have hg : (k + 3) ^ 2 ^ cdepth cg ≤ C := pow_pow_mono k (le_max_right _ _)
      have hC2 : 2 ≤ C := le_trans (by omega) (base_le_pow_pow k _)
      have hmax : max a b + 2 ≤ C := by
        rcases le_total a b with hab' | hab' <;> simp [hab'] <;> omega
      have hlt : Nat.pair a b < (max a b + 1) ^ 2 := pair_lt_sq a b
      have hsq : (max a b + 1) ^ 2 ≤ (C - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hCC : (C - 1) ^ 2 + 2 ≤ C * C := by
        have h' : (C - 1) ^ 2 = (C - 1) * (C - 1) := by ring
        have h'' : C - 1 + 1 = C := by omega
        nlinarith [hC2, h'']
      omega
    | comp cf cg ihf ihg =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff] at h
      obtain ⟨hn, a, ha, hb⟩ := h
      have h1 : m + 2 ≤ (k + 3) ^ 2 ^ cdepth cf := ihf a m hb
      show m + 2 ≤ (k + 3) ^ 2 ^ (1 + max (cdepth cf) (cdepth cg))
      exact h1.trans (pow_pow_mono k (by omega))
    | prec cf cg ihf ihg =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff] at h
      obtain ⟨hn, h2⟩ := h
      show m + 2 ≤ (k + 3) ^ 2 ^ (1 + max (cdepth cf) (cdepth cg))
      cases hy : (Nat.unpair n).2 with
      | zero =>
        rw [hy] at h2
        simp at h2
        have h1 : m + 2 ≤ (k + 3) ^ 2 ^ cdepth cf := ihf _ _ h2
        exact h1.trans (pow_pow_mono k (by omega))
      | succ y =>
        rw [hy] at h2
        simp [Option.bind_eq_some_iff] at h2
        obtain ⟨i, -, h3⟩ := h2
        have h1 : m + 2 ≤ (k + 3) ^ 2 ^ cdepth cg := ihg _ _ h3
        exact h1.trans (pow_pow_mono k (by omega))
    | rfind' cf ihf =>
      intro n m h
      simp [evaln, Option.bind_eq_some_iff] at h
      obtain ⟨hn, a, ha, h2⟩ := h
      show m + 2 ≤ (k + 3) ^ 2 ^ (1 + cdepth cf)
      by_cases ha0 : a = 0
      · simp [ha0] at h2
        have hmn : m ≤ n := by rw [← h2]; exact Nat.unpair_right_le n
        have h3 : k + 3 ≤ (k + 3) ^ 2 ^ (cdepth cf) := base_le_pow_pow k _
        rw [pow_pow_succ]
        nlinarith
      · simp [ha0] at h2
        have hrec := ihk k (by omega) (Code.rfind' cf) _ _ h2
        simp only [cdepth] at hrec ⊢
        exact hrec.trans (Nat.pow_le_pow_left (by omega) _)

/-! ### Running time -/

/-- The running time of the program `c` on input `x`: the least step bound sufficing to
produce an output (`0` if `c` diverges on `x`). -/
noncomputable def timeOf (c : Code) (x : ℕ) : ℕ := sInf {k | (evaln k c x).isSome}

theorem timeOf_le {c : Code} {x k v : ℕ} (h : evaln k c x = some v) : timeOf c x ≤ k :=
  Nat.sInf_le (by simp [Set.mem_setOf_eq, h])

theorem evaln_timeOf {c : Code} {x v : ℕ} (h : v ∈ eval c x) :
    evaln (timeOf c x) c x = some v := by
  obtain ⟨k, hk⟩ := evaln_complete.1 h
  have hk' : evaln k c x = some v := hk
  have hne : {k | (evaln k c x).isSome}.Nonempty := ⟨k, by simp [Set.mem_setOf_eq, hk']⟩
  have hmem : (evaln (timeOf c x) c x).isSome := Nat.sInf_mem hne
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hmem
  have hw' : w ∈ eval c x := evaln_sound hw
  rw [hw, Part.mem_unique h hw']

/-! ### The programs -/

/-- Code for the constant `1`. -/
def oneCode : Code := Code.comp Code.succ Code.zero

/-- Code for the predecessor function. -/
def predCode : Code :=
  Code.comp (Code.prec Code.zero (Code.comp Code.left Code.right)) (Code.pair Code.zero Code.id)

/-- Step of the loop computing `gfun`. -/
def baseBody : Code :=
  Code.pair (Code.comp Code.succ (Code.comp Code.left Code.right)) (Code.comp Code.right Code.right)

/-- The straightforward program computing `gfun` by a loop. -/
def baseCode : Code :=
  Code.comp (Code.prec oneCode baseBody) (Code.pair Code.zero Code.id)

/-- The family of ever faster programs for `gfun`: `fastCode (n+1)` computes `gfun x` as
`Nat.pair x (gfun (x-1))`, where the recursive value is produced by `fastCode n`.  Each extra
layer moves one squaring outside of the guarded part of the computation, thereby (roughly)
taking a square root of the running time. -/
def fastCode : ℕ → Code
  | 0 => baseCode
  | (n + 1) => Code.pair Code.id (Code.comp (fastCode n) predCode)

/-- Running time budget sufficient for `fastCode n` on input `x`. -/
def bud (n x : ℕ) : ℕ := (gfun (x - n) + 2) ^ 4 + (x + 2) ^ 4 + x + 2

theorem evaln_oneCode {k n : ℕ} (h : n ≤ k) : evaln (k + 1) oneCode n = some 1 := by
  rw [oneCode, evaln_comp' h, evaln_zero' h]
  simp [evaln_succ' (Nat.zero_le k)]

theorem evaln_id' {k n : ℕ} (h : n ≤ k) : evaln (k + 1) Code.id n = some n := by
  rw [Code.id, evaln_pair' h, evaln_left' h, evaln_right' h]; simp [Seq.seq]

theorem pair_pair_bound (a b : ℕ) : Nat.pair 0 (Nat.pair a b) < (max a b + 1) ^ 4 := by
  have h2 : Nat.pair 0 (Nat.pair a b) < (Nat.pair a b + 1) ^ 2 := by
    simpa using pair_lt_sq 0 (Nat.pair a b)
  calc Nat.pair 0 (Nat.pair a b) < (Nat.pair a b + 1) ^ 2 := h2
    _ ≤ ((max a b + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by have := pair_lt_sq a b; omega) 2
    _ = (max a b + 1) ^ 4 := by ring

theorem evaln_predLoop (y : ℕ) : ∀ k : ℕ, (y + 2) ^ 4 + y + 2 ≤ k →
    evaln k (Code.prec Code.zero (Code.comp Code.left Code.right)) (Nat.pair 0 y)
      = some (y - 1) := by
  induction y with
  | zero =>
    intro k hk
    obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
    rw [evaln_prec_zero' (show Nat.pair 0 0 ≤ K by rw [show Nat.pair 0 0 = 0 from rfl]; omega),
      evaln_zero' (Nat.zero_le K)]
  | succ y ih =>
    intro k hk
    obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
    have hKy : (y + 3) ^ 4 + y + 3 ≤ K + 1 := by
      have h : (y + 1 + 2) ^ 4 = (y + 3) ^ 4 := by norm_num
      omega
    have hmono : (y + 2) ^ 4 ≤ (y + 3) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have hguard : Nat.pair 0 (y + 1) ≤ K := by
      have h1 : Nat.pair 0 (y + 1) < (y + 2) ^ 2 := by simpa using pair_lt_sq 0 (y + 1)
      have h2 : (y + 2) ^ 2 ≤ (y + 3) ^ 4 := by nlinarith [sq_nonneg y]
      omega
    rw [evaln_prec_succ' hguard, ih K (by omega)]
    simp only [Option.bind_some]
    have hz : Nat.pair y (y - 1) < (y + 1) ^ 2 := by
      have hm : max y (y - 1) = y := by omega
      simpa [hm] using pair_lt_sq y (y - 1)
    have hzK : Nat.pair y (y - 1) ≤ K := by
      have h2 : (y + 1) ^ 2 ≤ (y + 3) ^ 4 := by nlinarith [sq_nonneg y]
      omega
    have hv : Nat.pair 0 (Nat.pair y (y - 1)) < (y + 1) ^ 4 := by
      have hm : max y (y - 1) = y := by omega
      simpa [hm] using pair_pair_bound y (y - 1)
    have hvK : Nat.pair 0 (Nat.pair y (y - 1)) ≤ K := by
      have h : (y + 1) ^ 4 ≤ (y + 3) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      omega
    rw [evaln_comp' hvK, evaln_right' hvK]
    simp only [Nat.unpair_pair, Option.bind_some]
    rw [evaln_left' hzK]
    simp

theorem evaln_predCode {x k : ℕ} (h : (x + 2) ^ 4 + x + 2 ≤ k) :
    evaln k predCode x = some (x - 1) := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  have hpow : x + 2 ≤ (x + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hx : x ≤ K := by omega
  rw [predCode, evaln_comp' hx, evaln_pair' hx, evaln_zero' hx, evaln_id' hx]
  simp only [Seq.seq]
  exact evaln_predLoop x (K + 1) h

theorem evaln_baseBody {K y g : ℕ} (hvK : Nat.pair 0 (Nat.pair y g) ≤ K)
    (hzK : Nat.pair y g ≤ K) (hyK : y ≤ K) :
    evaln (K + 1) baseBody (Nat.pair 0 (Nat.pair y g)) = some (Nat.pair (y + 1) g) := by
  have hA : evaln (K + 1) (Code.comp Code.succ (Code.comp Code.left Code.right))
      (Nat.pair 0 (Nat.pair y g)) = some (y + 1) := by
    rw [evaln_comp' hvK, evaln_comp' hvK, evaln_right' hvK]
    simp only [Nat.unpair_pair, Option.bind_some]
    rw [evaln_left' hzK]
    simp only [Nat.unpair_pair, Option.bind_some]
    exact evaln_succ' hyK
  have hB : evaln (K + 1) (Code.comp Code.right Code.right) (Nat.pair 0 (Nat.pair y g))
      = some g := by
    rw [evaln_comp' hvK, evaln_right' hvK]
    simp only [Nat.unpair_pair, Option.bind_some]
    rw [evaln_right' hzK]
    simp
  rw [baseBody, evaln_pair' hvK, hA, hB]
  simp [Seq.seq]

theorem evaln_baseLoop (y : ℕ) : ∀ k : ℕ, (gfun y + 2) ^ 4 + y + 2 ≤ k →
    evaln k (Code.prec oneCode baseBody) (Nat.pair 0 y) = some (gfun y) := by
  induction y with
  | zero =>
    intro k hk
    obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
    rw [evaln_prec_zero' (show Nat.pair 0 0 ≤ K by rw [show Nat.pair 0 0 = 0 from rfl]; omega),
      evaln_oneCode (Nat.zero_le K)]
    rfl
  | succ y ih =>
    intro k hk
    obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
    have hgy : gfun y ≤ gfun (y + 1) := gfun_le_succ y
    have hy1 : y + 1 ≤ gfun (y + 1) := self_le_gfun (y + 1)
    have hK : (gfun (y + 1) + 2) ^ 4 + y + 3 ≤ K + 1 := by
      have h : (gfun (y + 1) + 2) ^ 4 + (y + 1) + 2 ≤ K + 1 := hk
      omega
    have hGmono : (gfun y + 2) ^ 4 ≤ (gfun (y + 1) + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have hsq : ∀ t : ℕ, t ≤ gfun (y + 1) + 2 → t ^ 2 ≤ (gfun (y + 1) + 2) ^ 4 := by
      intro t ht
      calc t ^ 2 ≤ (gfun (y + 1) + 2) ^ 2 := Nat.pow_le_pow_left ht 2
        _ ≤ (gfun (y + 1) + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have hguard : Nat.pair 0 (y + 1) ≤ K := by
      have h1 : Nat.pair 0 (y + 1) < (y + 2) ^ 2 := by simpa using pair_lt_sq 0 (y + 1)
      have h2 := hsq (y + 2) (by omega)
      omega
    rw [evaln_prec_succ' hguard, ih K (by omega)]
    simp only [Option.bind_some]
    have hm : max y (gfun y) = gfun y := by have := self_le_gfun y; omega
    have hz : Nat.pair y (gfun y) < (gfun y + 1) ^ 2 := by simpa [hm] using pair_lt_sq y (gfun y)
    have hzK : Nat.pair y (gfun y) ≤ K := by
      have h2 := hsq (gfun y + 1) (by omega)
      omega
    have hv : Nat.pair 0 (Nat.pair y (gfun y)) < (gfun y + 1) ^ 4 := by
      simpa [hm] using pair_pair_bound y (gfun y)
    have hvK : Nat.pair 0 (Nat.pair y (gfun y)) ≤ K := by
      have h : (gfun y + 1) ^ 4 ≤ (gfun (y + 1) + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      omega
    rw [evaln_baseBody hvK hzK (by omega)]
    rfl

theorem evaln_baseCode {x k : ℕ} (h : (gfun x + 2) ^ 4 + x + 2 ≤ k) :
    evaln k baseCode x = some (gfun x) := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  have h1 : x ≤ gfun x := self_le_gfun x
  have hpow : gfun x + 2 ≤ (gfun x + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hx : x ≤ K := by omega
  rw [baseCode, evaln_comp' hx, evaln_pair' hx, evaln_zero' hx, evaln_id' hx]
  simp only [Seq.seq]
  exact evaln_baseLoop x (K + 1) h

theorem evaln_fastCode : ∀ (n x k : ℕ), bud n x ≤ k → evaln k (fastCode n) x = some (gfun x) := by
  intro n
  induction n with
  | zero =>
    intro x k hk
    rw [fastCode]
    refine evaln_baseCode ?_
    have h : bud 0 x = (gfun x + 2) ^ 4 + (x + 2) ^ 4 + x + 2 := by simp [bud]
    omega
  | succ n ih =>
    intro x k hk
    have hbud0 : (gfun (x - (n + 1)) + 2) ^ 4 + (x + 2) ^ 4 + x + 2 ≤ k := hk
    have hpow : x + 2 ≤ (x + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
    obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
    have hx : x ≤ K := by omega
    rw [fastCode, evaln_pair' hx, evaln_id' hx, evaln_comp' hx,
      evaln_predCode (x := x) (k := K + 1) (by omega)]
    simp only [Option.bind_some]
    have hstep : bud n (x - 1) ≤ K + 1 := by
      have h1 : x - 1 - n = x - (n + 1) := by omega
      have h2 : (x - 1 + 2) ^ 4 ≤ (x + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      simp only [bud, h1]
      omega
    rw [ih (x - 1) (K + 1) hstep]
    simp only [Seq.seq]
    exact congrArg some (gfun_eq_pair x).symm

theorem eval_fastCode (n : ℕ) : eval (fastCode n) = fun x => Part.some (gfun x) := by
  funext x
  exact Part.eq_some_iff.2 (evaln_sound (evaln_fastCode n x (bud n x) le_rfl))

theorem timeOf_fastCode_le (n x : ℕ) : timeOf (fastCode n) x ≤ bud n x :=
  timeOf_le (evaln_fastCode n x (bud n x) le_rfl)

/-! ### Lower bound on the running time of any program for `gfun` -/

theorem timeOf_lower_bound {c : Code} (hc : eval c = fun x => Part.some (gfun x)) (x : ℕ)
    (hx : cdepth c + 1 ≤ x) : 2 ^ 2 ^ (x - 1 - cdepth c) ≤ timeOf c x + 2 := by
  have hmem : gfun x ∈ eval c x := by rw [hc]; exact Part.mem_some _
  have hev : evaln (timeOf c x) c x = some (gfun x) := evaln_timeOf hmem
  have hout : gfun x + 2 ≤ (timeOf c x + 2) ^ 2 ^ cdepth c :=
    evaln_output_bound _ _ _ _ hev
  have hlow : 2 ^ 2 ^ (x - 1) ≤ gfun x := by
    have h := tower_le_gfun (x - 1)
    rwa [show x - 1 + 1 = x by omega] at h
  by_contra hcon
  push_neg at hcon
  have hpow : (timeOf c x + 2) ^ 2 ^ cdepth c < (2 ^ 2 ^ (x - 1 - cdepth c)) ^ 2 ^ cdepth c :=
    Nat.pow_lt_pow_left hcon (by positivity)
  have hexp : (2 ^ 2 ^ (x - 1 - cdepth c) : ℕ) ^ 2 ^ cdepth c = 2 ^ 2 ^ (x - 1) := by
    rw [← pow_mul, ← pow_add]
    congr 2
    omega
  rw [hexp] at hpow
  omega

/-! ### Upper bound on the running time of the fast programs -/

theorem bud_le_tower (n x : ℕ) (hx : 2 * n + 60 ≤ x) : bud n x ≤ 2 ^ 2 ^ (x - n + 5) := by
  set m := x - n with hm
  have hmn : n + 60 ≤ m := by omega
  have hxm : x ≤ 2 * m := by omega
  -- the first summand
  have h1 : gfun m + 2 ≤ 2 ^ 2 ^ (m + 2) := by have := gfun_le_tower m; omega
  have h2 : (gfun m + 2) ^ 4 ≤ 2 ^ 2 ^ (m + 4) := by
    calc (gfun m + 2) ^ 4 ≤ (2 ^ 2 ^ (m + 2)) ^ 4 := Nat.pow_le_pow_left h1 4
      _ = 2 ^ (2 ^ (m + 2) * 4) := by rw [← pow_mul]
      _ = 2 ^ 2 ^ (m + 4) := by
            congr 1
            have h : (2 : ℕ) ^ (m + 4) = 2 ^ (m + 2) * 4 := by
              rw [show m + 4 = (m + 2) + 2 by omega, pow_add]; norm_num
            omega
  -- the polynomial summand
  have h3 : (x + 2) ^ 4 + x + 2 ≤ 2 ^ x := by
    have := quartic_le_two_pow x (by omega)
    omega
  have h4 : x ≤ 2 ^ (m + 4) := by
    have h5 : 2 * m ≤ 2 ^ m := two_mul_le_two_pow m (by omega)
    have h6 : (2 : ℕ) ^ m ≤ 2 ^ (m + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h7 : (2 : ℕ) ^ x ≤ 2 ^ 2 ^ (m + 4) := Nat.pow_le_pow_right (by norm_num) h4
  -- combine
  have h8 : (2 : ℕ) ^ 2 ^ (m + 4) + 2 ^ 2 ^ (m + 4) ≤ 2 ^ 2 ^ (m + 5) := by
    have h9 : (2 : ℕ) ^ 2 ^ (m + 4) + 2 ^ 2 ^ (m + 4) = 2 ^ (2 ^ (m + 4) + 1) := by
      rw [pow_succ]; ring
    rw [h9]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have h10 : (2 : ℕ) ^ (m + 5) = 2 ^ (m + 4) * 2 := by rw [pow_succ]
    have h11 : 1 ≤ (2 : ℕ) ^ (m + 4) := Nat.one_le_two_pow
    omega
  have hb : bud n x = (gfun m + 2) ^ 4 + ((x + 2) ^ 4 + x + 2) := by simp only [bud, hm]; ring
  rw [hb, show x - n + 5 = m + 5 from rfl]
  omega

/-! ### Main theorem -/

/-- The heart of the matter: for every program `c` computing `gfun`, the program
`fastCode (cdepth c + 8)` also computes `gfun` and is, on all large inputs, faster than `c`;
in fact even the cube of its running time is at most the running time of `c`. -/
theorem speedup_core {c : Code} (hc : eval c = fun x => Part.some (gfun x)) :
    ∀ x, 2 * (cdepth c + 8) + 60 ≤ x →
      timeOf (fastCode (cdepth c + 8)) x ^ 3 ≤ timeOf c x ∧
        timeOf (fastCode (cdepth c + 8)) x < timeOf c x := by
  intro x hx
  set d := cdepth c with hd
  set A := (2 : ℕ) ^ 2 ^ (x - d - 3) with hA
  -- upper bound for the fast program
  have hup : timeOf (fastCode (d + 8)) x ≤ A := by
    have h1 : timeOf (fastCode (d + 8)) x ≤ bud (d + 8) x := timeOf_fastCode_le _ _
    have h2 : bud (d + 8) x ≤ 2 ^ 2 ^ (x - (d + 8) + 5) := bud_le_tower _ _ (by omega)
    have h3 : x - (d + 8) + 5 = x - d - 3 := by omega
    rw [h3] at h2
    omega
  -- lower bound for an arbitrary program computing `gfun`
  have hlow : 2 ^ 2 ^ (x - 1 - d) ≤ timeOf c x + 2 := timeOf_lower_bound hc x (by omega)
  have hexp : (2 : ℕ) ^ 2 ^ (x - 1 - d) = A ^ 4 := by
    rw [hA, ← pow_mul]
    congr 1
    rw [show x - 1 - d = (x - d - 3) + 2 by omega, pow_add]
    ring
  rw [hexp] at hlow
  have hA2 : 2 ≤ A := by
    rw [hA]
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ 2 ^ (x - d - 3) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  have hA3 : 8 ≤ A ^ 3 := by simpa using Nat.pow_le_pow_left hA2 3
  have hcube : A ^ 3 + 2 ≤ A ^ 4 :=
    calc A ^ 3 + 2 ≤ A ^ 3 + A ^ 3 := by omega
      _ = 2 * A ^ 3 := by ring
      _ ≤ A * A ^ 3 := Nat.mul_le_mul_right _ hA2
      _ = A ^ 4 := by ring
  have hlin : A + 3 ≤ A ^ 3 :=
    calc A + 3 ≤ A * 4 := by omega
      _ ≤ A * A ^ 2 := Nat.mul_le_mul_left A (by simpa using Nat.pow_le_pow_left hA2 2)
      _ = A ^ 3 := by ring
  have hfast : timeOf (fastCode (d + 8)) x ^ 3 ≤ A ^ 3 := Nat.pow_le_pow_left hup 3
  exact ⟨by omega, by omega⟩

/-- **Blum speedup**: there is a problem with no fastest algorithm.  Concretely, there is a total
computable function `f` (namely `gfun`) such that every program `c` computing `f` is beaten, on
all but finitely many inputs, by another program `d` computing `f`. -/
theorem blum_speedup :
    ∃ f : ℕ → ℕ,
      (∃ c : Code, eval c = fun x => Part.some (f x)) ∧
      ∀ c : Code, eval c = (fun x => Part.some (f x)) →
        ∃ d : Code, eval d = (fun x => Part.some (f x)) ∧
          ∀ᶠ x in Filter.atTop, timeOf d x < timeOf c x := by
  refine ⟨gfun, ⟨fastCode 0, eval_fastCode 0⟩, fun c hc => ⟨fastCode (cdepth c + 8),
    eval_fastCode _, ?_⟩⟩
  rw [Filter.eventually_atTop]
  exact ⟨2 * (cdepth c + 8) + 60, fun x hx => (speedup_core hc x hx).2⟩

/-- A quantitative form of the speedup: the faster program's running time is eventually at most
the *cube root* of the running time of the given program. -/
theorem blum_speedup_cube :
    ∃ f : ℕ → ℕ,
      (∃ c : Code, eval c = fun x => Part.some (f x)) ∧
      ∀ c : Code, eval c = (fun x => Part.some (f x)) →
        ∃ d : Code, eval d = (fun x => Part.some (f x)) ∧
          ∀ᶠ x in Filter.atTop, timeOf d x ^ 3 ≤ timeOf c x := by
  refine ⟨gfun, ⟨fastCode 0, eval_fastCode 0⟩, fun c hc => ⟨fastCode (cdepth c + 8),
    eval_fastCode _, ?_⟩⟩
  rw [Filter.eventually_atTop]
  exact ⟨2 * (cdepth c + 8) + 60, fun x hx => (speedup_core hc x hx).1⟩

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

