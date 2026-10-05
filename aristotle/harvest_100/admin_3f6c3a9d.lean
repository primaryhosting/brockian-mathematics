/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
## Overview

This file formalises the *hardness versus randomness* theorem of Impagliazzo and
Wigderson: strong (exponential) circuit lower bounds imply `P = BPP`.

The development is self contained (it uses only the Lean 4 core library) and is
organised in three clearly separated layers.

* **Boolean circuits and pseudorandomness.**  Boolean circuits, their size, the
  number of accepted inputs of a Boolean function, and the notion of a *pseudorandom
  generator* (a map on short seeds whose output distribution `1/12`-fools every small
  circuit) are defined concretely.  The derandomisation gap lemma
  (`CS.fooled_gap`) — the combinatorial heart of the argument — is proved from
  scratch: a fooled circuit whose acceptance probability is at least `2/3` accepts a
  strict majority of the generator's seeds, and one whose acceptance probability is at
  most `1/3` does not.

* **An abstract model of deterministic polynomial time.**  Rather than fixing a
  Turing machine model, the structure `CS.Model` axiomatises the standard closure
  properties of deterministic polynomial time that the argument needs: a deterministic
  algorithm is a randomised algorithm ignoring its randomness (`poly2_const`), a
  polynomial-time randomised algorithm is simulated on each input by a polynomial-size
  circuit acting on its random bits (`circuit_sim`, Cook–Levin), and polynomial time is
  closed under taking a majority vote over a polynomially large seed space
  (`derandomize`).  The classes `Model.P` and `Model.BPP` are then defined in the usual
  way, `BPP` with the standard two-sided error bounds `2/3` and `1/3`.

* **The Nisan–Wigderson / Impagliazzo–Wigderson generator.**  The construction of a
  pseudorandom generator with logarithmic seed length out of an exponentially hard
  function is taken as an explicit hypothesis `hIW` of the main theorem; the strong
  circuit lower bound itself is the hypothesis `hHard`.

The main theorem `CS.impagliazzo_wigderson` then proves `BPP = P`.  Both inclusions
are established; the substantial one derandomises an arbitrary `BPP` algorithm by
taking the majority vote of its answers over all seeds of the generator.

Randomness is modelled by a natural number `k < 2 ^ m` whose bits `k.testBit i`,
`i < m`, are the `m` random bits; the uniform distribution on `{0,1}^m` is therefore
the uniform distribution on `{0, …, 2^m - 1}`, and probabilities are expressed as
counting inequalities between natural numbers.
-/

namespace CS

/-- Binary strings, the inputs of our algorithms. -/
abbrev Str := List Bool

/-- A language is a predicate on binary strings. -/
abbrev Lang := Str → Bool

/-! ### Counting -/

/-- `countLt p N` is the number of `k < N` with `p k = true`. -/
def countLt (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => countLt p n + (if p n = true then 1 else 0)

/-- Two predicates agreeing below `N` are counted equally. -/
theorem countLt_congr {p q : Nat → Bool} :
    ∀ N : Nat, (∀ k, k < N → p k = q k) → countLt p N = countLt q N
  | 0, _ => rfl
  | N + 1, h => by
    have hlt : ∀ k, k < N → p k = q k := fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hN : p N = q N := h N (Nat.lt_succ_self N)
    simp [countLt, countLt_congr N hlt, hN]

/-! ### Boolean circuits -/

/-- Boolean circuits (formulas over `¬`, `∧`, `∨`) whose variables are indexed by
natural numbers. -/
inductive Circuit : Type
  | const (b : Bool) : Circuit
  | var (i : Nat) : Circuit
  | not (c : Circuit) : Circuit
  | and (c₁ c₂ : Circuit) : Circuit
  | or (c₁ c₂ : Circuit) : Circuit

namespace Circuit

/-- Evaluation of a circuit on the input whose `i`-th bit is `k.testBit i`. -/
def eval : Circuit → Nat → Bool
  | .const b, _ => b
  | .var i, k => k.testBit i
  | .not c, k => !(c.eval k)
  | .and c₁ c₂, k => (c₁.eval k) && (c₂.eval k)
  | .or c₁ c₂, k => (c₁.eval k) || (c₂.eval k)

/-- The number of gates of a circuit. -/
def size : Circuit → Nat
  | .const _ => 1
  | .var _ => 1
  | .not c => c.size + 1
  | .and c₁ c₂ => c₁.size + c₂.size + 1
  | .or c₁ c₂ => c₁.size + c₂.size + 1

/-- `C.usesOnly m` says that `C` only reads the input bits `0, …, m - 1`, i.e. that
`C` is a circuit on `m` inputs. -/
def usesOnly : Circuit → Nat → Bool
  | .const _, _ => true
  | .var i, m => decide (i < m)
  | .not c, m => c.usesOnly m
  | .and c₁ c₂, m => c₁.usesOnly m && c₂.usesOnly m
  | .or c₁ c₂, m => c₁.usesOnly m && c₂.usesOnly m

end Circuit

/-! ### Pseudorandom generators -/

/-- `Fools G l m s` says that the generator `G`, mapping seeds `u < 2 ^ l` to strings
`G u < 2 ^ m`, has an output distribution that is `1/12`-indistinguishable from the
uniform distribution on `{0,1}^m` by every circuit of size at most `s` on `m` inputs.

Writing `a` for the number of accepting seeds and `b` for the number of accepting
inputs, the two displayed inequalities are the two halves of
`|a / 2 ^ l - b / 2 ^ m| ≤ 1 / 12`, cleared of denominators. -/
def Fools (G : Nat → Nat) (l m s : Nat) : Prop :=
  ∀ C : Circuit, C.usesOnly m = true → C.size ≤ s →
    12 * countLt (fun u => C.eval (G u)) (2 ^ l) * 2 ^ m
        ≤ 12 * countLt C.eval (2 ^ m) * 2 ^ l + 2 ^ l * 2 ^ m ∧
      12 * countLt C.eval (2 ^ m) * 2 ^ l
        ≤ 12 * countLt (fun u => C.eval (G u)) (2 ^ l) * 2 ^ m + 2 ^ l * 2 ^ m

/-- Arithmetic core of the derandomisation, accepting case: if `b / M ≥ 2 / 3` and
`|a / L - b / M| ≤ 1 / 12`, then `a / L > 1 / 2`. -/
theorem gap_yes {a b L M : Nat} (hL : 0 < L) (hM : 0 < M)
    (h : 12 * b * L ≤ 12 * a * M + L * M) (hb : 2 * M ≤ 3 * b) : L < 2 * a := by
  have h1 : (4 * L) * (2 * M) ≤ (4 * L) * (3 * b) := Nat.mul_le_mul_left _ hb
  have h2 : (7 * L) * M ≤ (12 * a) * M := by grind
  have h3 : 7 * L ≤ 12 * a := Nat.le_of_mul_le_mul_right h2 hM
  omega

/-- Arithmetic core of the derandomisation, rejecting case: if `b / M ≤ 1 / 3` and
`|a / L - b / M| ≤ 1 / 12`, then `a / L ≤ 1 / 2`. -/
theorem gap_no {a b L M : Nat} (hM : 0 < M)
    (h : 12 * a * M ≤ 12 * b * L + L * M) (hb : 3 * b ≤ M) : 2 * a ≤ L := by
  have h1 : (4 * L) * (3 * b) ≤ (4 * L) * M := Nat.mul_le_mul_left _ hb
  have h2 : (12 * a) * M ≤ (5 * L) * M := by grind
  have h3 : 12 * a ≤ 5 * L := Nat.le_of_mul_le_mul_right h2 hM
  omega

/-- **The derandomisation gap lemma.**  If `G` `1/12`-fools all circuits of size `s`
on `m` inputs and `C` is such a circuit, then the majority vote of `C` over all seeds
of `G` reproduces the answer of `C` under the uniform distribution, provided the
latter has two-sided error at most `1/3`. -/
theorem fooled_gap {G : Nat → Nat} {l m s : Nat} (hG : Fools G l m s) {C : Circuit}
    (hu : C.usesOnly m = true) (hs : C.size ≤ s) :
    (2 * 2 ^ m ≤ 3 * countLt C.eval (2 ^ m) →
        2 ^ l < 2 * countLt (fun u => C.eval (G u)) (2 ^ l)) ∧
      (3 * countLt C.eval (2 ^ m) ≤ 2 ^ m →
        2 * countLt (fun u => C.eval (G u)) (2 ^ l) ≤ 2 ^ l) := by
  obtain ⟨h1, h2⟩ := hG C hu hs
  have hL : 0 < 2 ^ l := Nat.two_pow_pos l
  have hM : 0 < 2 ^ m := Nat.two_pow_pos m
  exact ⟨fun hyes => gap_yes hL hM h2 hyes, fun hno => gap_no hM h1 hno⟩

/-! ### Growth rates -/

/-- `f` is polynomially bounded. -/
def PolyBound (f : Nat → Nat) : Prop := ∃ a : Nat, ∀ n, f n ≤ (n + 2) ^ a

/-- The seed length `l` is logarithmic, i.e. the seed space `{0,1}^{l n}` has only
polynomially many elements. -/
def SeedBound (l : Nat → Nat) : Prop := ∃ a : Nat, ∀ n, 2 ^ l n ≤ (n + 2) ^ a

/-- The number of random strings on which the randomised algorithm `A`, using `m |x|`
random bits, accepts the input `x`. -/
def accCount (A : Str → Nat → Bool) (m : Nat → Nat) (x : Str) : Nat :=
  countLt (A x) (2 ^ m x.length)

/-! ### An abstract model of deterministic polynomial time -/

/-- An abstract model of deterministic polynomial-time computation.

Rather than committing to a concrete machine model we record those closure properties
of deterministic polynomial time that the derandomisation argument uses.  Every
standard machine model (multitape Turing machines, RAMs, …) satisfies them. -/
structure Model where
  /-- `Poly1 f`: the language `f` is decidable in deterministic polynomial time. -/
  Poly1 : (Str → Bool) → Prop
  /-- `Poly2 A`: the randomised algorithm `A`, taking an input string and a random
  string (encoded as a natural number), runs in deterministic polynomial time. -/
  Poly2 : (Str → Nat → Bool) → Prop
  /-- `InE f`: the family `f` of Boolean functions (`f n` is a function of `n` input
  bits, presented as a number `< 2 ^ n`) is computable in deterministic time
  `2 ^ O(n)`, i.e. it lies in the class `E`. -/
  InE : (Nat → Nat → Bool) → Prop
  /-- `PolyGen l G`: the generator family `G`, with seed length `l n` on inputs of
  length `n`, is computable in deterministic polynomial time. -/
  PolyGen : (Nat → Nat) → (Nat → Nat → Nat) → Prop
  /-- A deterministic polynomial-time algorithm is in particular a randomised
  polynomial-time algorithm which ignores its randomness. -/
  poly2_const : ∀ f : Str → Bool, Poly1 f → Poly2 (fun x _ => f x)
  /-- Cook–Levin style simulation: for a polynomial-time randomised algorithm `A`
  using `m n` random bits on inputs of length `n`, there is a polynomial size bound
  `s` such that for every input `x` the map `r ↦ A x r` is computed on all `m |x|`-bit
  strings by a circuit on `m |x|` inputs of size at most `s |x|`. -/
  circuit_sim : ∀ (A : Str → Nat → Bool) (m : Nat → Nat), Poly2 A → PolyBound m →
    ∃ s : Nat → Nat, PolyBound s ∧ ∀ x : Str, ∃ C : Circuit,
      C.usesOnly (m x.length) = true ∧ C.size ≤ s x.length ∧
        ∀ k, k < 2 ^ m x.length → C.eval k = A x k
  /-- Deterministic polynomial time is closed under taking the majority vote of a
  polynomial-time randomised algorithm over the polynomially many outputs of a
  polynomial-time generator with logarithmic seed length. -/
  derandomize : ∀ (A : Str → Nat → Bool) (l : Nat → Nat) (G : Nat → Nat → Nat),
    Poly2 A → PolyGen l G → SeedBound l →
    Poly1 (fun x => decide (2 ^ l x.length <
      2 * countLt (fun u => A x (G x.length u)) (2 ^ l x.length)))

namespace Model

variable (M : Model)

/-- The class `P`: languages decidable in deterministic polynomial time. -/
def P (L : Lang) : Prop := M.Poly1 L

/-- The class `BPP`: languages decided by a polynomial-time randomised algorithm whose
error probability is at most `1/3` on every input. -/
def BPP (L : Lang) : Prop :=
  ∃ (A : Str → Nat → Bool) (m : Nat → Nat), M.Poly2 A ∧ PolyBound m ∧
    ∀ x : Str,
      (L x = true → 2 * 2 ^ m x.length ≤ 3 * accCount A m x) ∧
      (L x = false → 3 * accCount A m x ≤ 2 ^ m x.length)

/-- **The strong circuit lower bound hypothesis**: some language in the class `E`
requires Boolean circuits of size `2 ^ Ω(n)`. -/
def StrongCircuitLowerBound : Prop :=
  ∃ f : Nat → Nat → Bool, M.InE f ∧ ∃ c : Nat, 0 < c ∧ ∃ N : Nat,
    ∀ n, N ≤ n → ∀ C : Circuit, C.usesOnly n = true →
      (∀ k, k < 2 ^ n → C.eval k = f n k) → 2 ^ (n / c) ≤ C.size

/-- The conclusion of the Nisan–Wigderson / Impagliazzo–Wigderson generator
construction: for every polynomial output length `m` and every polynomial circuit size
bound `s` there is a polynomial-time computable generator with logarithmic seed length
whose output distribution `1/12`-fools every circuit of size `s` on `m` inputs. -/
def HasIWGenerator : Prop :=
  ∀ m s : Nat → Nat, PolyBound m → PolyBound s →
    ∃ (l : Nat → Nat) (G : Nat → Nat → Nat),
      SeedBound l ∧ M.PolyGen l G ∧
      (∀ n u, G n u < 2 ^ m n) ∧
      ∀ n, Fools (G n) (l n) (m n) (s n)

end Model

/-! ### Consistency of the model axioms -/

/-- A model witnessing that the axioms collected in `CS.Model` are consistent: the
randomised algorithms are the ones that ignore their randomness, and every language is
declared to be polynomial time.  (This is of course a degenerate model; its only
purpose is to rule out a vacuous reading of the main theorem.) -/
def degenerateModel : Model where
  Poly1 := fun _ => True
  Poly2 := fun A => ∀ x r r', A x r = A x r'
  InE := fun _ => True
  PolyGen := fun _ _ => True
  poly2_const := fun _ _ _ _ _ => rfl
  circuit_sim := by
    intro A m hA _
    refine ⟨fun _ => 1, ⟨0, by simp⟩, fun x => ⟨Circuit.const (A x 0), rfl, ?_, ?_⟩⟩
    · simp [Circuit.size]
    · intro k _
      exact hA x 0 k
  derandomize := by intros; trivial

/-- The assumptions gathered in `CS.Model` are satisfiable. -/
theorem nonempty_model : Nonempty Model := ⟨degenerateModel⟩

/-! ### The two inclusions -/

/-- Every language decidable in deterministic polynomial time lies in `BPP`: run the
deterministic algorithm and ignore the randomness. -/
theorem P_subset_BPP (M : Model) (L : Lang) (hL : M.P L) : M.BPP L := by
  refine ⟨fun x _ => L x, fun _ => 0, M.poly2_const L hL, ⟨0, by simp⟩, ?_⟩
  intro x
  have hcount : accCount (fun x _ => L x) (fun _ => 0) x
      = if L x = true then 1 else 0 := by
    simp [accCount, countLt]
  constructor
  · intro hx
    rw [hcount]
    simp [hx]
  · intro hx
    rw [hcount]
    simp [hx]

/-- **Derandomisation.**  Given the pseudorandom generators produced by the
Impagliazzo–Wigderson construction, every `BPP` language is decidable in deterministic
polynomial time: replace the random string by the output of the generator and take the
majority vote over all (polynomially many) seeds. -/
theorem BPP_subset_P_of_generator (M : Model) (hG : M.HasIWGenerator) (L : Lang)
    (hL : M.BPP L) : M.P L := by
  obtain ⟨A, m, hA, hm, hAL⟩ := hL
  -- polynomial size circuits simulating `A` on each input
  obtain ⟨s, hs, hsim⟩ := M.circuit_sim A m hA hm
  -- a generator fooling all those circuits
  obtain ⟨l, G, hl, hPG, hGlt, hfool⟩ := hG m s hm hs
  -- the derandomised algorithm decides `L`
  have hD := M.derandomize A l G hA hPG hl
  have hEq : (fun x => decide (2 ^ l x.length <
      2 * countLt (fun u => A x (G x.length u)) (2 ^ l x.length))) = L := by
    funext x
    obtain ⟨C, hCu, hCs, hCe⟩ := hsim x
    have hseed : countLt (fun u => A x (G x.length u)) (2 ^ l x.length)
        = countLt (fun u => C.eval (G x.length u)) (2 ^ l x.length) :=
      countLt_congr _ (fun u _ => (hCe _ (hGlt x.length u)).symm)
    have hunif : countLt (A x) (2 ^ m x.length) = countLt C.eval (2 ^ m x.length) :=
      countLt_congr _ (fun k hk => (hCe k hk).symm)
    obtain ⟨hyes, hno⟩ := fooled_gap (hfool x.length) hCu hCs
    rw [hseed]
    cases hLx : L x
    · have h := hno (by
        have := (hAL x).2 hLx
        rw [accCount, hunif] at this
        exact this)
      simp only [decide_eq_false_iff_not, Nat.not_lt]
      omega
    · have h := hyes (by
        have := (hAL x).1 hLx
        rw [accCount, hunif] at this
        exact this)
      simp [h]
  rw [hEq] at hD
  exact hD

/-! ### The Impagliazzo–Wigderson theorem -/

/-- **Impagliazzo–Wigderson: strong circuit lower bounds imply `P = BPP`.**

In any model of deterministic polynomial-time computation satisfying the standard
closure properties collected in `CS.Model`, if some language of `E` requires Boolean
circuits of size `2 ^ Ω(n)` (`hHard`), and hence, by the Nisan–Wigderson generator
construction (`hIW`), there are polynomial-time computable pseudorandom generators
with logarithmic seed length fooling all polynomial-size circuits, then `BPP = P`. -/
theorem impagliazzo_wigderson (M : Model)
    (hIW : M.StrongCircuitLowerBound → M.HasIWGenerator)
    (hHard : M.StrongCircuitLowerBound) :
    ∀ L : Lang, M.BPP L ↔ M.P L :=
  fun L => ⟨BPP_subset_P_of_generator M (hIW hHard) L, P_subset_BPP M L⟩

end CS

