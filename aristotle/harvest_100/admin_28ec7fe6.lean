/-!
# Ed 25519 Verify Sound
Category: Proof-Carrying Apps
Target: PCA.Cert.ed25519_verify_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## An abstract model of Ed25519 signature verification

We model the Ed25519 signature scheme inside the prime-order subgroup of the
twisted Edwards curve `edwards25519`.  The group is kept abstract: it is any
commutative group `G` (class `PCA.Cert.PointGroup`) together with a base point
`B` whose additive order is the Ed25519 group order

  `ell = 2^252 + 27742317777372353535851937790883648493`.

Scalars are natural numbers acting on points by repeated addition
(`PCA.Cert.PointGroup.nsmul`).  The challenge hash `H` (computing
`k = H(R, A, M)`) is abstract as well: no property of it is assumed, so all the
results below hold for every instantiation of the hash.

Main results:

* `PCA.Cert.ed25519_verify_complete` -- honestly produced signatures verify;
* `PCA.Cert.ed25519_verify_sound`    -- conversely, if the verification equation
  holds for the public key `A = s * B` and the signature's commitment is
  `R = r * B`, then the signature is *exactly* the honest signature for the
  secret scalar `s`, nonce `r` and message `m`.  In other words the verifier
  accepts no pair `(R, S)` other than the unique one prescribed by the Ed25519
  signing equation `S = r + H(R, A, M) * s  (mod ell)`.

The development is self-contained: it depends only on the Lean 4 core library.
-/

namespace PCA.Cert

/-- The order of the prime-order subgroup of `edwards25519` used by Ed25519. -/
def ell : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

theorem ell_pos : 0 < ell :=
  Nat.lt_of_lt_of_le
    (show 0 < 27742317777372353535851937790883648493 by omega)
    (Nat.le_add_left _ _)

/-- An abstract commutative group of curve points, written additively. -/
class PointGroup (G : Type u) where
  add : G → G → G
  zero : G
  neg : G → G
  add_assoc : ∀ a b c : G, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : G, add a b = add b a
  zero_add : ∀ a : G, add zero a = a
  neg_add : ∀ a : G, add (neg a) a = zero

namespace PointGroup

variable {G : Type u} [PointGroup G]

theorem add_zero (a : G) : add a zero = a := by
  rw [add_comm, zero_add]

theorem add_neg (a : G) : add a (neg a) = zero := by
  rw [add_comm]; exact neg_add a

theorem add_left_cancel {a b c : G} (h : add a b = add a c) : b = c := by
  have h2 : add (neg a) (add a b) = add (neg a) (add a c) := congrArg _ h
  rwa [← add_assoc, ← add_assoc, neg_add, zero_add, zero_add] at h2

theorem add_right_cancel {a b c : G} (h : add a c = add b c) : a = b := by
  refine add_left_cancel (a := c) ?_
  rw [add_comm c a, add_comm c b]
  exact h

/-- `nsmul n P` is the `n`-fold sum `P + ... + P`. -/
def nsmul : Nat → G → G
  | 0, _ => zero
  | (n + 1), P => add P (nsmul n P)

@[simp] theorem nsmul_zero (P : G) : nsmul 0 P = zero := rfl

theorem nsmul_succ (n : Nat) (P : G) : nsmul (n + 1) P = add P (nsmul n P) := rfl

@[simp] theorem nsmul_zero_point (n : Nat) : nsmul n (zero : G) = zero := by
  induction n with
  | zero => rfl
  | succ k ih => rw [nsmul_succ, ih, zero_add]

theorem nsmul_add (m n : Nat) (P : G) :
    nsmul (m + n) P = add (nsmul m P) (nsmul n P) := by
  induction m with
  | zero => rw [Nat.zero_add, nsmul_zero, zero_add]
  | succ k ih =>
    have hk : k + 1 + n = (k + n) + 1 := by omega
    rw [hk, nsmul_succ, ih, nsmul_succ, add_assoc]

theorem nsmul_mul (m n : Nat) (P : G) :
    nsmul (m * n) P = nsmul m (nsmul n P) := by
  induction m with
  | zero => rw [Nat.zero_mul, nsmul_zero, nsmul_zero]
  | succ k ih =>
    rw [Nat.succ_mul, nsmul_add, ih, nsmul_succ, add_comm]

end PointGroup

open PointGroup

section BasePoint

variable {G : Type u} [PointGroup G] {B : G}

/-- `B` has order (dividing) `ell`. -/
theorem nsmul_eq_zero_of_dvd (hell : nsmul ell B = zero) {n : Nat} (h : ell ∣ n) :
    nsmul n B = zero := by
  obtain ⟨q, rfl⟩ := h
  rw [Nat.mul_comm, nsmul_mul, hell, nsmul_zero_point]

/-- Reducing a scalar modulo the group order does not change the resulting point. -/
theorem nsmul_mod (hell : nsmul ell B = zero) (n : Nat) :
    nsmul (n % ell) B = nsmul n B := by
  have hdm : ell * (n / ell) + n % ell = n := Nat.div_add_mod n ell
  have h : nsmul (ell * (n / ell) + n % ell) B = nsmul n B := by rw [hdm]
  rwa [nsmul_add, nsmul_eq_zero_of_dvd hell ⟨n / ell, rfl⟩, zero_add] at h

/-- If no smaller positive multiple of `B` vanishes, then `n * B = 0` forces
`ell ∣ n`. -/
theorem dvd_of_nsmul_eq_zero (hell : nsmul ell B = zero)
    (hmin : ∀ n : Nat, 0 < n → n < ell → nsmul n B ≠ zero)
    {n : Nat} (h : nsmul n B = zero) : ell ∣ n := by
  have h1 : nsmul (n % ell) B = zero := by rw [nsmul_mod hell, h]
  rcases Nat.eq_zero_or_pos (n % ell) with h0 | hpos
  · exact Nat.dvd_of_mod_eq_zero h0
  · exact absurd h1 (hmin _ hpos (Nat.mod_lt _ ell_pos))

theorem nsmul_inj_aux (hell : nsmul ell B = zero)
    (hmin : ∀ n : Nat, 0 < n → n < ell → nsmul n B ≠ zero)
    {m n : Nat} (hle : n ≤ m) (h : nsmul m B = nsmul n B) : m % ell = n % ell := by
  have hsplit : nsmul (m - n) B = zero := by
    refine add_right_cancel (c := nsmul n B) ?_
    rw [← nsmul_add, Nat.sub_add_cancel hle, h, zero_add]
  obtain ⟨k, hk⟩ := dvd_of_nsmul_eq_zero hell hmin hsplit
  have hm : m = n + ell * k := by omega
  rw [hm, Nat.add_mul_mod_self_left]

/-- Scalars acting equally on the base point are congruent modulo `ell`. -/
theorem nsmul_inj (hell : nsmul ell B = zero)
    (hmin : ∀ n : Nat, 0 < n → n < ell → nsmul n B ≠ zero)
    {m n : Nat} (h : nsmul m B = nsmul n B) : m % ell = n % ell := by
  rcases Nat.le_total n m with hle | hle
  · exact nsmul_inj_aux hell hmin hle h
  · exact (nsmul_inj_aux hell hmin hle h.symm).symm

end BasePoint

/-- Messages are finite bit strings. -/
abbrev Message := List Bool

/-- An Ed25519 signature: a curve point `R` together with a scalar `S`. -/
structure Signature (G : Type u) where
  R : G
  S : Nat

/-- The public key belonging to the secret scalar `s`. -/
def publicKey {G : Type u} [PointGroup G] (B : G) (s : Nat) : G := nsmul s B

/-- Ed25519 signing with secret scalar `s`, nonce `r` and challenge hash `H`. -/
def sign {G : Type u} [PointGroup G] (H : G → G → Message → Nat) (B : G)
    (s r : Nat) (m : Message) : Signature G where
  R := nsmul r B
  S := (r + H (nsmul r B) (publicKey B s) m * s) % ell

/-- Ed25519 verification: the scalar must be canonically reduced and the group
equation `S * B = R + H(R, A, M) * A` must hold. -/
def verify {G : Type u} [PointGroup G] (H : G → G → Message → Nat) (B A : G)
    (m : Message) (sig : Signature G) : Prop :=
  sig.S < ell ∧ nsmul sig.S B = add sig.R (nsmul (H sig.R A m) A)

/-- **Completeness**: an honestly generated Ed25519 signature always verifies. -/
theorem ed25519_verify_complete {G : Type u} [PointGroup G] {B : G}
    (hell : nsmul ell B = zero) (H : G → G → Message → Nat) (s r : Nat)
    (m : Message) :
    verify H B (publicKey B s) m (sign H B s r m) := by
  refine ⟨Nat.mod_lt _ ell_pos, ?_⟩
  show nsmul ((r + H (nsmul r B) (publicKey B s) m * s) % ell) B
      = add (nsmul r B) (nsmul (H (nsmul r B) (publicKey B s) m) (publicKey B s))
  rw [nsmul_mod hell, nsmul_add, publicKey, ← nsmul_mul]

/-- **Soundness of Ed25519 verification.**

Let `B` be a base point of order `ell`, `A = s * B` a public key and let a
candidate signature `sig` carry the commitment `R = r * B`.  If `sig` passes
verification, then `sig` is *exactly* the honest signature produced by `sign`
from the secret scalar `s`, the nonce `r` and the message `m`; in particular its
scalar component satisfies `S = r + H(R, A, M) * s (mod ell)`.

Thus the verifier accepts no point/scalar pair other than the unique one
prescribed by the Ed25519 signing equation. -/
theorem ed25519_verify_sound {G : Type u} [PointGroup G] {B : G}
    (hell : nsmul ell B = zero)
    (hmin : ∀ n : Nat, 0 < n → n < ell → nsmul n B ≠ zero)
    (H : G → G → Message → Nat) (s r : Nat) (m : Message) (sig : Signature G)
    (hR : sig.R = nsmul r B)
    (hv : verify H B (publicKey B s) m sig) :
    sig = sign H B s r m := by
  obtain ⟨hlt, heq⟩ := hv
  cases sig with
  | mk R S =>
    simp only at hR heq hlt
    subst hR
    have heq' : nsmul S B
        = nsmul (r + H (nsmul r B) (publicKey B s) m * s) B := by
      rw [nsmul_add, nsmul_mul]
      exact heq
    have hmod : S % ell = (r + H (nsmul r B) (publicKey B s) m * s) % ell :=
      nsmul_inj hell hmin heq'
    have hS : S = (r + H (nsmul r B) (publicKey B s) m * s) % ell := by
      rw [← hmod, Nat.mod_eq_of_lt hlt]
    rw [hS]
    rfl


/-!
## Non-vacuity: a concrete group of order `ell`

To make sure that the hypotheses of `ed25519_verify_sound` are satisfiable we
exhibit a concrete cyclic group of order `ell` together with a generator.  (Of
course the intended instance is the prime-order subgroup of `edwards25519`, but
the proofs above are valid for any such group.)
-/

/-- The residues modulo `ell`, a concrete cyclic group of order `ell`. -/
structure Zell where
  val : Nat
  isLt : val < ell

namespace Zell

theorem ext {a b : Zell} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

instance : PointGroup Zell where
  add a b := ⟨(a.val + b.val) % ell, Nat.mod_lt _ ell_pos⟩
  zero := ⟨0, ell_pos⟩
  neg a := ⟨(ell - a.val) % ell, Nat.mod_lt _ ell_pos⟩
  add_assoc a b c := by
    refine ext ?_
    show ((a.val + b.val) % ell + c.val) % ell
        = (a.val + (b.val + c.val) % ell) % ell
    rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
  add_comm a b := by
    refine ext ?_
    show (a.val + b.val) % ell = (b.val + a.val) % ell
    rw [Nat.add_comm]
  zero_add a := by
    refine ext ?_
    show (0 + a.val) % ell = a.val
    rw [Nat.zero_add, Nat.mod_eq_of_lt a.isLt]
  neg_add a := by
    refine ext ?_
    show ((ell - a.val) % ell + a.val) % ell = 0
    rw [Nat.mod_add_mod, Nat.sub_add_cancel (Nat.le_of_lt a.isLt), Nat.mod_self]

theorem one_lt_ell : 1 < ell :=
  Nat.lt_of_lt_of_le
    (show 1 < 27742317777372353535851937790883648493 by omega)
    (Nat.le_add_left _ _)

/-- The canonical generator `1` of `Zell`. -/
def gen : Zell := ⟨1, one_lt_ell⟩

theorem nsmul_gen (n : Nat) :
    PointGroup.nsmul n gen = ⟨n % ell, Nat.mod_lt _ ell_pos⟩ := by
  induction n with
  | zero =>
    refine ext ?_
    show 0 = 0 % ell
    rw [Nat.zero_mod]
  | succ k ih =>
    refine ext ?_
    rw [PointGroup.nsmul_succ, ih]
    show (1 + k % ell) % ell = (k + 1) % ell
    rw [Nat.add_mod_mod, Nat.add_comm]

theorem gen_order : PointGroup.nsmul ell gen = PointGroup.zero := by
  refine ext ?_
  rw [nsmul_gen]
  show ell % ell = 0
  rw [Nat.mod_self]

theorem gen_order_min (n : Nat) (hpos : 0 < n) (hlt : n < ell) :
    PointGroup.nsmul n gen ≠ PointGroup.zero := by
  rw [nsmul_gen]
  intro h
  have : n % ell = 0 := congrArg Zell.val h
  rw [Nat.mod_eq_of_lt hlt] at this
  omega

end Zell

/-- Soundness of Ed25519 verification, instantiated in the concrete cyclic
group `Zell` of order `ell`; this witnesses that the hypotheses of
`ed25519_verify_sound` are satisfiable. -/
theorem ed25519_verify_sound_Zell (H : Zell → Zell → Message → Nat) (s r : Nat)
    (m : Message) (sig : Signature Zell) (hR : sig.R = nsmul r Zell.gen)
    (hv : verify H Zell.gen (publicKey Zell.gen s) m sig) :
    sig = sign H Zell.gen s r m :=
  ed25519_verify_sound Zell.gen_order Zell.gen_order_min H s r m sig hR hv

end PCA.Cert

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

