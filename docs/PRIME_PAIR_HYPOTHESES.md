# Prime-pair hypotheses: terminology and use

The project uses two deliberately different conjectural interfaces.

| Interface | Mathematical scope | Required theorem binder |
|---|---|---|
| `PrimePairsInAPAtModulus q g` | One fixed modulus and gap | `(h : Hypothesis.PrimePairsInAPAtModulus q g)` |
| `UniformPrimePairsInAP g Q` | Every `q` with `3 ≤ q ≤ Q(X)` | `(h : Hypothesis.UniformPrimePairsInAP g Q)` |

The second is stronger whenever `Q(X)` grows. A theorem using it must state `Q`; a
phrase such as “uniform in arithmetic progressions” without a range is incomplete.

Neither interface is a consequence of Bombieri–Vinogradov. The standard theorem
concerns individual primes in progressions, whereas these interfaces concern a prime-pair
correlation. A generalized Hardy–Littlewood formulation may be stated at fixed modulus;
that is why fixed-modulus and uniform-range claims must not share an identifier.

## Migration policy

Legacy interfaces whose names merge prime-pair conjectures with Bombieri–Vinogradov are
quarantined. Their finite algebra and limit lemmas may be ported only after conditional
theorems visibly carry one of the propositions above. No theorem may receive an implicit
instance of either proposition.

## Public wording

Use: “conditional on the explicitly named prime-pairs-in-AP hypothesis over the stated
modulus range.”

Do not use: “a Bombieri–Vinogradov form,” “proved equidistribution,” or language that
conceals the range `Q(X)`.
