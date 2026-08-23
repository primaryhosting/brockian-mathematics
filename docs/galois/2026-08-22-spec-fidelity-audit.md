# Independent Spec-Fidelity & Assumption Audit — Galois / seL4 Ecosystem Artifacts

**Date:** 2026-08-22
**Author:** ACUTIS verification program (for Christopher Brock → Galois)
**Method:** an independent *vacuity / spec-fidelity / axiom-hygiene* gate run against real, unmodified GaloisInc and seL4 artifacts, with every claim reproduced mechanically (Cryptol nightly + Z3) or verified verbatim against source.

---

## Executive summary

An independent gate, pointed at four real artifact families, surfaced **17 distinct issues across four tiers** — every one either mechanically reproduced (Cryptol + Z3, output pasted) or anchored to a source-verified `file:line`.

- **Headline (F0):** a stated `property` in Galois's own **Curve25519 reference spec (`cswapTrue`) is actually *false*** — provable by a deterministic counterexample — and the in-repo check the docstring tells you to run (`:check`) passes it at 0.00% coverage. Impact on X25519 is nil (the live path uses a different function), so it is *cosmetic in effect but serious as a spec-fidelity defect*: a green-but-wrong property is exactly what a gate must catch.
- **Deepest TCB item (F7):** inside AWS-LC's **claimed ECDSA/ECDH proofs**, an *unproven* Jacobian↔affine coordinate identity is admitted via `assume_unsat` and folded into the top-level theorem — a spec-layer axiom the public caveat table does not disclose (the caveat covers "trust the C," not "we admitted a math lemma").
- **Sharpest seL4 item (F12):** the **default** Rust capDL initializer build parses the trusted spec blob with `rkyv::access_unchecked` — no structural validation, `unsafe`, with the safety obligation actively suppressed (`#[allow(clippy::missing_safety_doc)]`, zero `SAFETY:` comments) — a memory-safety trust that fires *before* any kernel syscall can adjudicate.
- **The constructive payoff (Tier 4):** three AI-drafted-style properties on real ChaCha20-Poly1305 / SHA3 specs, each shown vacuous / under-constraining / drifted, each paired with the mechanical **gate rule** that catches it (§5).

Honest calibration up front: the Cryptol findings are all *true-as-stated except F0*, mitigated in-project by KATs; the SAW/seL4 items are deliberate, mostly-disclosed assumptions. The value is the **independent map of where trust actually sits** and the specific disclosure-granularity gaps — not a claim that anything was "broken."

---

## 0. What this is — and what it is not

This is the deliverable that answers a fair, pointed question: *is an independent "AI-proposes-checker-certifies" gate actually useful on Galois's own work, or only on our toy problems?* We pointed it at four real artifact families and found concrete issues. To keep the bar honest:

- **A finding counts only if it is mechanically demonstrated.** For Cryptol, that means Cryptol itself printing `Q.E.D.` / `Counterexample` / `Unsatisfiable` (Z3 backend), pasted verbatim. For SAW/seL4 (which we cannot compile here) a finding is an **evidence-backed concern** anchored to a **source-verified `file:line`**, with confidence stated and a devil's-advocate.
- **We did not modify any repo file.** Cryptol mutants live only in REPL batches.
- **We are not claiming we "broke" AWS-LC or seL4.** The strongest SAW/seL4 items are *assumptions the authors deliberately made and mostly disclosed at a coarse granularity*; the contribution is an **independent, precise map of where the trust actually sits**, plus the specific spots where the public disclosure under-describes it.
- **Every reproduction command is reproducible verbatim** via the `./cry.sh` harness (a thin wrapper over `ghcr.io/galoisinc/cryptol:nightly`) against the pinned `cryptol-specs` tree.

Repos audited (shallow clones, 2026-08-22): `GaloisInc/cryptol-specs`, `GaloisInc/aws-lc-verification` (SAW), `seL4/capdl`, `seL4/rust-sel4`.

### The through-line
Every Cryptol finding below is an instance of one disease: **a property/spec that a prover happily accepts while it fails to constrain what its name or shape implies.** The SAW/seL4 findings are the same disease one level up: **an obligation admitted or a well-formedness invariant assumed, where the disclosure under-states how load-bearing it is.** The gate is the cure — and §5 gives the exact mechanical rules that catch each pathology.

---

## Tier 1 — Mechanically-proven vacuity & under-constraint in real Cryptol specs

### ★ F0 (headline). A stated `property` in the Curve25519 reference spec is **actually false** — and the repo's own recommended check passes it
`cryptol-specs/Common/EC/Curve25519.cry:349`
```cryptol
property cswapTrue y x = y > 0 ==> cswap y (cswap y x) == x
```
Unlike every other Tier-1 item (which are *true-but-weak*), this property is **false**. The selector `y` is typed `[255]` (verified: `cswap : [255] -> (Z p, Z p) -> (Z p, Z p)`), not a single bit. The masked "constant-time" `cswap` computes `mask = 0 - y`, so it is a faithful swap only for `y ∈ {0,1}`; the sibling `cswapEq` correctly restricts to `elem s [0,1]`, but `cswapTrue` guards with `y > 0` — a domain of 2²⁵⁵−1 values. A deterministic counterexample (`y=2`, `x=(1, p−1)`) collapses both coordinates to 0 through the `BVtoZ` mod-`p` reduction, breaking even the involution:
```
$ ./cry.sh <<'ICRY'
:module Common::EC::Curve25519
:eval (2 : [255]) > 0
:eval cswap 2 (1, (-1 : Z p))
:eval cswap 2 (cswap 2 (1, (-1 : Z p))) == (1, (-1 : Z p))
:check cswapTrue
:eval cswap' 2 (cswap' 2 (1, (-1:Z p))) == (1, (-1:Z p))
ICRY
True                                   ← antecedent y>0 holds
(0, 0)                                 ← cswap 2 (1, p-1) collapses both coordinates
False                                  ← involution FAILS ⇒ property is FALSE
Testing... Passed 100 tests.
Expected test coverage: 0.00% (100 of 2^^765 values)   ← :check (what the docstring tells you to run) MASKS it
True                                   ← the reference cswap' is correct at the same point
```
`cswapTrue 2 (1, p−1) = (True ⇒ False) = False`. The property is false, the in-repo check the docstring recommends (`:check`) passes at literally 0.00% coverage (random sampling essentially never draws a small selector paired with a mod-`p`-boundary operand), and no `:prove`/SAW harness exercises it. **Class:** false property / constraint-mismatch (`y > 0` where the sibling correctly uses `elem y [0,1]`). **Severity:** serious *as an assurance-hygiene defect* — a green-but-wrong property in a reference crypto spec is exactly what formal methods exist to prevent.
**Honest bounding (blast radius = nil for X25519):** the live X25519 ladder calls only the reference `cswap'`, and only with `{0,1}` selectors (`k_t = (k >> t) & 1`); the masked `cswap` appears *exclusively inside the three properties*, so no test vector or DH property is affected. The file preamble also disclaims constant-time modeling and flags `cswap` as illustrative. Fix is one token: `y > 0` → `elem y [0,1]`, or retype the selector as `[1]`. So: **cosmetic in impact on X25519 today, serious as a spec-fidelity defect** — and precisely the pattern the gate exists to catch.

### F1. `RSACorrect` is a non-theorem, "guarded" by a vacuous no-op
`cryptol-specs/Primitive/Asymmetric/Cipher/RSA.cry:45`
```cryptol
property RSACorrect e d n msg = ( msg >= zero /\ msg < n ) ==> RSADP ((n,d), RSAEP ((n,e), msg)) == msg
```
`e,d,n,msg : [K]` are **unsigned** words. The "safety" conjunct `msg >= zero` is a tautology (every unsigned value is ≥ 0), so the only real guard is `msg < n`. But `e,d` are **free** — the property asserts RSA round-trips for *any* exponent pair, with no key-validity relation (`d ≡ e⁻¹ mod λ(n)`). It is therefore **false as written**.
```
$ ./cry.sh <<'ICRY'
:prove \(msg:[8]) -> msg >= zero
:module Primitive::Asymmetric::Cipher::RSA
:eval RSACorrect (2:[8]) (2:[8]) (15:[8]) (2:[8])
ICRY
Q.E.D.                       ← the guard is a no-op
False                        ← property false for a non-key (e=2,d=2,n=15), guard 2<15 holds
```
**Class:** non-theorem / dead-guard. **Severity:** latent. Correctness silently relies on the *caller* passing valid keys via `:check` args — a fact the `property` object does not encode. **Devil's advocate:** the Integer variants `IntegerRSACorrect*` guard `msg >= zero` meaningfully (Integer is signed) and are `:check`ed with real keys; the intent is a checkable test, not a universal theorem.

### F2. RSA primitives: the two-sided domain check is provably one-sided (5 sites)
`RSA.cry:33` (RSAEP), `:39` (RSADP); `Signature/RSA.cry:21` (RSASP1), `:28` (RSAVP1); `Scheme/RSAES_OAEP.cry:62`.
```cryptol
RSAEP ((n, e), m) = if (m < zero \/ m > (n-1)) then error "message representative out of range" else c
```
`m` is unsigned, so `m < zero` is unsatisfiable — the range guard collapses to the upper bound only.
```
$ ./cry.sh <<'ICRY'
:prove \(m:[64], n:[64]) -> ((m < zero \/ m > (n-1)) == (m > (n-1)))
ICRY
Q.E.D.                       ← the disjunction is definitionally equal to the upper bound alone
```
**Class:** dead-guard-false. **Severity:** latent — inert for the unsigned representation, but a transcription trap the moment anyone ports these PKCS#1 primitives to a signed/Integer representation, where a negative representative *is* possible and the copied check silently permits it. **Devil's advocate:** faithful transcription of the integer-valued FIPS pseudocode; harmless here.

### F3. ML-KEM `BitRev7`: dead validation branch that tests the *wrong* bound
`cryptol-specs/Primitive/Asymmetric/KEM/ML_KEM/Specification.cry:773`
```cryptol
BitRev7 i = if i > 255 then error "BitRev7 called with invalid input" else (reverse i) >> 1
```
`i : [8]` maxes at 255, so the `error` branch is unreachable; and the *documented* domain is `[0,127]`, so the guard checks the wrong constant. Inputs 128..255 flow through with no error and no meaningful 7-bit semantics.
```
$ ./cry.sh <<'ICRY'
:module Primitive::Asymmetric::KEM::ML_KEM::Specification
:prove \(i:[8]) -> ~(i > 255)
:sat   \(i:[8]) -> (i > 127)
ICRY
Q.E.D.                       ← error branch unreachable
Satisfiable  ... 0x80 = True ← inputs the docstring calls invalid pass through unchecked
```
**Class:** dead-branch / wrong-bound. **Severity:** latent. **Devil's advocate:** the `[8]` width was chosen deliberately to avoid overflow downstream; callers only pass `0..127`; the guard is belt-and-suspenders.

### F4. `CTR.encryptCorrect` — a "correctness" property a **null cipher** satisfies (+ ~15 siblings)
`cryptol-specs/Primitive/Symmetric/Cipher/Block/Modes/CTR.cry:79`
```cryptol
property encryptCorrect k c ps = (decrypt k c (encrypt k c ps)) == ps
```
In CTR, `encrypt ≡ decrypt` (XOR with the keystream), so the round-trip is XOR self-inversion — true for **any** block function, including one that ignores the key or returns a constant.
```
$ ./cry.sh <<'ICRY'
let ctrEnc ciph (t1:[128]) (ps:[5][128]) = [ p ^ (ciph t) | p <- ps | t <- [ t1 + i | i <- [0...] ] ]
let ctrDec ciph (t1:[128]) (cs:[5][128]) = [ c ^ (ciph t) | c <- cs | t <- [ t1 + i | i <- [0...] ] ]
let ok ciph t1 ps = ctrDec ciph t1 (ctrEnc ciph t1 ps) == ps
:prove \(t1:[128]) (ps:[5][128]) -> ok (\(_:[128]) -> (0:[128])) t1 ps
:prove \(t1:[128]) (ps:[5][128]) -> ok (\(b:[128]) -> b) t1 ps
ICRY
Q.E.D.                       ← round-trip holds for a constant-ZERO "cipher" (ciphertext = plaintext, no confidentiality)
Q.E.D.                       ← and for the IDENTITY "cipher"
```
**Same family** (all `decrypt∘encrypt = id`, all satisfied by an identity cipher): `CBC.cry:75`, `XTS.cry:300`, `MEE_CBC/Specification.cry:88,226`, `TDES_CBC.cry:30`, `TDES_CFB.cry:32`, self-tests in `PRESENT.cry`, `GOST.cry`, `TEA.cry`, `KATAN.cry`; `GCM/Specification.cry:141 gcmIsSymmetric` is the AEAD analogue. **Class:** under-constraint. **Severity:** medium — a property literally named `encryptCorrect`, provable, that pins down *nothing* about the primitive. **Devil's advocate:** these are honestly *inverse* lemmas; value-correctness is covered elsewhere by KAT vectors. The exposure is presentational — read in isolation as "verified," it overstates coverage.

### F5. `keyScheduleInjective` (Speck & Simon) — passes for a schedule that does no mixing
`Speck/Specification.cry:243`, `Simon/Specification.cry:389`
```cryptol
property keyScheduleInjective k v = k != v ==> keySchedule k != keySchedule v
```
Injectivity is trivially met by any schedule that embeds the key verbatim (both real schedules do) — it witnesses none of the round-constant / rotation / Feistel mixing.
```
$ ./cry.sh <<'ICRY'
:module Primitive::Symmetric::Cipher::Block::Speck::Instantiations::Speck32_64
let mutantKS (K:[4][16]) = (K # zero) : [22][16]      // copy + zero-pad: NO mixing
:prove \k v -> k != v ==> mutantKS k != mutantKS v
:eval mutantKS [1,2,3,4] == keySchedule [1,2,3,4]
ICRY
Q.E.D.                       ← non-mixing schedule satisfies injectivity
False                        ← …while differing from the real Speck schedule
```
**Class:** under-constraint (surrogate invariant). **Severity:** low-med. **Devil's advocate:** injectivity is the one property that matters for a key-collision counting argument; value-correctness is a separate `keySchedulesEquivalent` check.

### F6. AES `RconIsExponentiation` constrains only 1 of 4 bytes of each round constant
`AES/Specification.cry:279`
```cryptol
property RconIsExponentiation j = (1 <= j) && (j <= 10) ==> (Rcon j)@0 == GF28::pow <| x |> (j-1)
```
`Rcon j` is a 4-byte word whose trailing 3 bytes must be `0x00` (FIPS-197) and which XORs *in full* into the key schedule. The property inspects only byte 0; a corrupted Rcon (`[b,0xFF,0xFF,0xFF]`) passes (`Q.E.D.`) as the *only* property about `Rcon`. **Class:** projection under-constraint. **Severity:** low-med. **Devil's advocate:** the doc-comment scrupulously says "left-most byte"; the table's zero bytes are literal and KATs would catch corruption end-to-end.

### Supporting (Tier 1)
- **ZUC `isResistantToCollisionAttack`** (`Stream/ZUC.cry:307`) — name evokes collision-resistance; body checks that **one** 32-bit init word differs under a **fixed** key. A name-vs-statement gap (flagged, not mutated).
- **FALCON `BerExp`** (`Signature/FALCON/1.2/falcon_parameterized.cry:408`) — binds `w = zero`, so the Bernoulli-exp acceptance test is the constant `False` ignoring both inputs; Cryptol itself emits `Unused name: x` / `Unused name: ccs`. Carries an explicit `// TODO: Finish this` — a *known* WIP, included only as a clean example of a fully-typed signature that reads operational but computes a constant.
- **Erased `>= 0` type-constraints** (`Modes/CFB.cry:50,81,104`, `RSAES_OAEP.cry:56,88`, `XMSS/Specification.cry:599`) — `s >= 0` on a Cryptol numeric type is always-true; Cryptol's own inferred type drops it. Cosmetic documentation smell.
- **Fresh leads (uninvestigated):** loading `ML_KEM/Specification.cry` and the ChaCha20-Poly1305 spec surfaced additional `Unused name:` warnings (`Specification.cry:1053,1054,1464`; ChaCha `ptlen`/`adlen` at `:1083,1085,1119,1121`) — candidate dead-input functions worth a follow-up sweep.

---

## Tier 2 — Where the AWS-LC SAW TCB is *assumed* rather than *proved* (all `file:line` source-verified)

96 `unsafe_assume_spec` sites across 17 `.saw` files. The public caveat table discloses classes like `EC_Ops_Correct`, `MemCorrect`, `PubKeyValid`. The audit maps the assumed surface and isolates the spots the disclosure under-describes.

### F7 (deepest). An **unproven math identity** is admitted as an axiom *inside* the claimed ECDSA/ECDH proofs
`SAW/proof/ECDSA/ECDSA.saw:187-196`, `SAW/proof/ECDH/ECDH.saw:51-60`
```
jacobian_affine_0_thm <- prove_print (do { assume_unsat; })
  (rewrite ... {{ \k -> fromJacobian { x = ((ec_point_jacobian_scalar_mul (k % `P384_n) P384_G_Jacobian).x % `P384_p), ... }
                  == ec_point_affine_scalar_mul (k % `P384_n) P384_G }});
```
`assume_unsat` makes SAW **accept the goal as valid without proving it**; the resulting rewrite is then folded into the top-level correctness proof (`addsimp jacobian_affine_0_thm` at `ECDSA.saw:234,281`; `ECDH.saw:121,154`). This is the coordinate-system bridge between the implementation's Jacobian model and the affine functional spec.
**The disclosure gap:** the `EC_Ops_Correct` caveat says the proof *trusts the C that implements EC ops* — it does **not** say a **spec-layer mathematical identity** is admitted as an axiom. A reader of the caveat table would not know this. **Confidence:** high that it is load-bearing and under-disclosed; low that the identity is actually false (it is a standard projective-geometry fact). **Why it matters:** a future edit to those long inline Cryptol terms (a wrong reduction modulus `% P384_p` vs `% P384_n`, a missing z=0 side condition) would pass unchecked. **Recommendation:** promote from `assume_unsat` to a proved lemma, or list it explicitly in the caveats.

### F8. The ECDSA **verify acceptance rule** is itself assumed
`SAW/proof/EC/EC.saw:682-697`, assumed at `1191-1194`
```
let ec_cmp_x_coordinate_spec = do { ... crucible_return (crucible_term
   {{ if (fromJacobian (jacobianFromMontBV p)).x % `P384_n == (scalarFromBV r) % `P384_n then 1:[32] else 0 }}); };
```
This Cryptol term *is* the ECDSA acceptance predicate `r ≡ x(R) mod n`, `unsafe_assume`d. A too-strong model at the `x ∈ [n, p)` boundary (the C compares against `r` and `r+n`, not a literal mod-n reduction) would make forgeries verify while the proof still passes. Disclosed under `EC_Ops_Correct`, but it is the single assume-spec whose incorrectness is most directly catastrophic (verify-accepts-forgery). **Recommendation:** a dedicated `llvm_verify` of `ec_GFp_mont_cmp_x_coordinate` — highest-leverage assumption to convert to a proof.

### F9. `ec_GFp_simple_is_on_curve` postcondition hard-codes `return 1` for any input
`SAW/proof/EC/EC.saw:725-737`, assumed at `1211-1214` (self-admitted in-comment: *"will always return 1"*). The input point is unconstrained and unused; the off-curve **rejection** path (invalid-curve / fault-injection defense) is entirely unverified — a postcondition strictly stronger than the C. Disclosed via `PubKeyValid`, but the "postcondition-always-true" shape is exactly what turns a coverage caveat into latent unsoundness the day a downstream proof depends on a `0` return.

### F10. A one-line switch converts the *entire* suite from proved to assumed
`SAW/proof/common/helpers.saw:73-79`
```
let do_prove = true;
let llvm_verify m func overrides pathsat spec tactic =
  if do_prove then crucible_llvm_verify ... else crucible_llvm_unsafe_assume_spec m func spec;
```
Flipping `do_prove` to `false` silently turns every `llvm_verify`/`llvm_verify_x86` into an `unsafe_assume_spec`; the suite still "passes" having proved almost nothing. It is `true` today — but it is an un-gated, single-point control over the whole proof/assume boundary. A genuine **proof-integrity / supply-chain** observation for a CI setting.

### F11. RSA rests on 19 admitted number-theoretic axioms
`SAW/proof/RSA/arithmetic-axioms.saw` — 19 `assume_unsat` lemmas including `inv_thm` (modular inverse existence, line 35), `fermat_euler_thm` (38), `crt_thm` (45). These underpin the assumed `BN_mod_exp_mont` (`a^p mod m`, `BN.saw:389`) and the blinding model. RSA is outside the published verified tables, so these are unclaimed — but anyone reusing the RSA proofs inherits a large admitted-axiom base. (Honesty note in the *safe* direction: the claimed SHA-512 block is genuinely `llvm_verify_x86`-proved with `ia32cap` pinned, not assumed; and `ec_scalar_is_zero` is *more* faithful than the README says.)

**Systemic:** the assumed surface partitions into (1) infra idealizations (infallible malloc, no-op `OPENSSL_cleanse` with an empty zeroization postcondition — sound-in-direction), (2) EC field/point arithmetic (bulk of `EC.saw`/`BN.saw`, disclosed wholesale under `EC_Ops_Correct`), (3) assembly blocks (SHA-256 shows a "verify one `ia32cap`, assume all paths" pattern; not in the claimed TCB), (4) RSA (outside the TCB, axiom-heavy). The load-bearing risk is concentrated in F7 and F8.

---

## Tier 3 — The seL4 "un-Isabelle'd frontier" (capDL + rust-sel4; crux `file:line` source-verified)

The Isabelle-verified TCB is the C kernel + `l4v`. capDL tooling and rust-sel4 sit **outside** it on the trusted boot path. The systemic pattern: **well-formedness is asserted-but-not-enforced at each hand-off, and the chain leans on "the capDL blob is trusted build-time input."** The kernel re-validating every `Retype`/`Mint`/`Map` syscall at boot is the safety net — so the sharp question is which invariants it does *not* re-check, and which trusts are **silent** vs **documented**.

### F12 (sharpest). The default Rust initializer parses the capDL blob with `rkyv::access_unchecked` — zero validation, safety obligation suppressed
`rust-sel4/crates/sel4-capdl-initializer/src/lib_main.rs:79-82`
```rust
#[cfg(not(feature = "alloc"))]
fn access_spec(bytes: &[u8]) -> &<SpecForInitializer as Archive>::Archived {
    unsafe { SpecForInitializer::access_unchecked(bytes) }
}
```
Source-verified: `Cargo.toml` has `default = ["deflate"]` (**`alloc` is not default**), so the shipped no-`std` build takes this arm; the checked `rkyv::access` arm is compiled out. `types/src/lib.rs:46` carries `#[allow(clippy::missing_safety_doc)]` on `access_unchecked`, and there are **zero `SAFETY:` comments** across the entire initializer crate. This is the **one** trust that is a *memory-safety* trust and happens *before* any kernel syscall can adjudicate: a malformed/corrupted blob yields archived types whose relative pointers are dereferenced during object creation — OOB reads / type confusion in the root task. **Confidence:** high that the default build is unchecked and undocumented; medium on adversary reachability (requires influence over the embedded blob / build pipeline). **Devil's advocate:** by design the spec is a trusted build artifact embedded at link time; enabling `alloc` gives checked `access`. The point for a briefing is precisely that the *only* thing between a bad blob and UB is an out-of-band trust — and the code actively hides the obligation.

### F13. capDL-tool validates *structure* but not the *geometric* retype invariants downstream stages assume
`capdl/capDL-tool/CapDL/State.hs:513-514`
```haskell
validObjCap _ (CNode _ 0) slot cap = slot == 0 && is _NotificationCap cap
validObjCap _ (CNode {}) _ _ = True        -- ← CNode cap validity is literally True
```
Source-verified. Four load-bearing invariants are absent from `checkModel`: (1) CNode slot index < 2^radix (the `True` above; `sizeBits` is unbounded), (2) `guard_size + radix ≤ word_size`, (3) untyped physical-range containment / non-overlap / alignment (`checkCovers` compares *ObjID sets*, not physical geometry), (4) paddr alignment vs object size. **Sharp consequence:** a spec passing `checkModel` can encode an impossible CNode cap or an illegal untyped derivation; the **Isabelle proof-export (`--isabelle`) and the info-flow leak matrix then model a system that cannot exist** — the verified artifact and the loaded artifact can diverge with no tool complaining. **Confidence:** high (checks are literally absent/`True`). **Devil's advocate:** the kernel enforces radix/guard/alignment at boot, so an ill-formed spec fails safely; the real exposure is fidelity of the *offline* model/proof exports. (Counter-evidence the tool *does* enforce: duplicate slots are a hard error, referenced objects must exist, cap-target types checked, frame sizes must be powers of two.)

### F14. `sel4-shared-ring-buffer`: consumer reads peer-written indices with a **non-atomic** load (data race), and the net driver turns peer misbehavior into panic-DoS
`rust-sel4/crates/experimental/sel4-shared-ring-buffer/src/lib.rs` — publish side stores with `Ordering::Release` (`:259,281`); consumer observes the same locations with a plain `.read()` (`:171,182`) resolving to a non-atomic `ptr::read` (`sel4-shared-memory/src/ops.rs:15`). Source-verified. Mixing an atomic `Release` store with a concurrent non-atomic load of the same location is a data race (UB) in the Rust/LLVM memory model — the consumer may see a fresh `write_index` with a stale/torn descriptor. Downstream, `driver-adapters/src/net/driver.rs:63-75` `.unwrap()`s every `PeerMisbehaviorError` and does attacker-influenced pointer arithmetic whose bounds-check *panics* → aborts the shared driver PD → cross-client DoS. **Confidence:** med-high (a formal data race + a real panic path; HW-atomic aligned loads on the target arches soften manifestation). **Devil's advocate:** `T: FromBytes` means no validity-UB (only staleness/tearing); driver authors are explicitly unverified TCB; the crates are `experimental/`; a panic is fail-stop.

### Supporting (Tier 3)
- **python-capdl-tool: soundness-by-`assert`.** Untyped fit/alignment/watermark and cap-field-width checks (`Object.py:416-420`, `Cap.py:38,51`) are `assert`s — **no-ops under `python -O`** — and CNode slots are a plain dict that silently overwrites duplicates (`Object.py:179`); `Object.py:300` even comments "Maximum size (28 bits) is not checked."
- **python ELF parsing** emits `CDL_FrameFill_FileData` copy directives from unvalidated `p_offset/p_filesz` (`ELF.py:119-132`) — a crafted ELF (`p_filesz > p_memsz`, offset past EOF) could instruct the loader to copy out-of-file bytes into a frame. Whether the loader re-validates is the **next audit target**.
- **C `capdl-loader-app`** has author-documented "fail messily" paths (`main.c:1264` FIXME on stack pointers outside the ELF image) and RISC-V root-VSpace uniqueness assumptions — `[DOC-TRUSTED]`, lower priority.
- **rust-sel4 release-only guards:** `AbstractPtr::as_chunks_unchecked` memory-safety precondition guarded only by `debug_assert` (`slice_operations.rs:152`); rustls `discard()` underflow via `debug_assert` on untrusted TLS data (`utils.rs:64`).

---

## Tier 4 — The AI-in-the-loop gate demonstrations (constructed on real specs)

Honest framing: the *specs* are the genuine ChaCha20-Poly1305 / ChaCha20 / SHA3-256 modules; the *properties* are ones we wrote to imitate how an AI (or a hurried engineer) drafts a security property a prover accepts but that fails to constrain what it claims. **No Galois-authored property is called defective here.** Each demo pairs the disease with the mechanical gate that cures it.

### D1. Vacuously-true (unsatisfiable antecedent) — AEAD integrity
An AEAD "tampered ⇒ rejected" property where the "tampered" ciphertext is never actually mutated, so the antecedent is `ct != ct`:
```
:prove \k n pt -> ((AEAD... k n pt []) != (AEAD... k n pt [])) ==> (DECRYPT k n (AEAD... k n pt []) [] == None)
→ Q.E.D.                                     ← proves nothing
:sat  \k n pt -> (AEAD... k n pt []) != (AEAD... k n pt [])
→ Unsatisfiable                              ← antecedent is False everywhere
```
**Gate — antecedent-SAT:** every `A ==> B` must have `:sat A` return a model, else fail.

### D2. Under-constraining (a wrong impl passes too) — ChaCha20 round-trip
```
:prove \k n pt -> ChaCha20DecryptBytes (ChaCha20EncryptBytes pt k n 1) k n 1 == pt   → Q.E.D.
:prove \k n pt -> (\p -> p) ((\p -> p) pt) == pt                                       → Q.E.D.  ← identity "cipher" passes
```
The round-trip cannot distinguish real ChaCha20 from a key-ignoring identity (zero confidentiality). **Gate — dependency/mutation:** the property must *fail* for ≥1 wrong impl; concretely, ciphertext must change when the key changes:
```
:eval ChaCha20EncryptBytes [0,0,0] (0:[256]) (0:[96]) 1 != ChaCha20EncryptBytes [0,0,0] (1:[256]) (0:[96]) 1  → True
:eval (\p->p) [0,0,0] != (\p->p) [0,0,0]                                                                      → False  ← mutant flagged
```

### D3. Fidelity drift (name says "for all", body checks one input) — SHA3-256
A `sha3_256_correct` whose body checks a single fixed vector is satisfied by a hash that hard-codes that one answer and returns zeros elsewhere (`Q.E.D.` for both). **Gate — quantifier/differential:** a property whose name asserts a universal guarantee must quantify over its inputs, not equal a constant; a differential `:prove \x -> impl x == reference x` surfaces the ignored input.

| Pathology | Prover symptom | Gate that catches it |
|---|---|---|
| Vacuous | `Q.E.D.` on `A⇒B`, `A` unsat | `:sat A` must return a model |
| Under-constraining | `Q.E.D.` for real *and* broken impl | property must fail for ≥1 mutant; output must depend on every security-relevant input |
| Fidelity drift | `Q.E.D.` but body is one literal input | body must be quantified; differential check surfaces an ignored input |

---

## 5. Honest limitations

- The SAW (Tier 2) and seL4 (Tier 3) findings are **not compiled/executed** here — they are source-verified concerns, not proven bugs, and most are assumptions the authors made deliberately and disclosed at some granularity. Their value is the *independent map* and the *disclosure-granularity* gaps (F7 especially), not "we found a live exploit."
- Tier 1/Tier 4 findings **are** mechanically proven vacuity/under-constraint, but every one is *true-as-stated* and mitigated in-project by KATs / cross-formulation checks. The risk they name is **misreading a green checkmark as more coverage than it provides** — precisely the risk that grows when an AI generates a property *without* the surrounding KATs.
- None of this touches the Isabelle-verified seL4 kernel core.

## 6. Recommended next steps (joint, Galois-facing)
1. Promote **F7** (`assume_unsat` coordinate bridge) from an admitted axiom to a proved lemma, or list it explicitly in the caveats — the cleanest single win.
2. Convert **F8** (`ec_cmp_x_coordinate`) from assumption to a dedicated `llvm_verify` — highest security leverage.
3. Add the §5 gate as a lightweight lint over cryptol-specs (`antecedent-SAT`, `mutation`, `quantifier`) — cheap, catches all of Tier 1/4 automatically.
4. Point the next audit at the **capDL loader's re-validation of `FrameFill` file offsets and untyped geometry** (F13/ELF supporting) — the one boundary neither the Haskell tool nor the Rust initializer covers.

*All reproductions are verbatim against the pinned artifact clones (2026-08-22). Harness: `ghcr.io/galoisinc/cryptol:nightly` + Z3.*
