import Brockian.AutomorphismFull
import Brockian.D5Representation
import Brockian.D5Isotypic
import Brockian.D5FourierInversion
import Brockian.Fin5InnerProduct
import Brockian.D5LaplacianModes
import Brockian.PentagonIsotypic
import Brockian.PentagonMultiplicities
import Brockian.PentagonEquivariance
import Brockian.PentagonCharacterMultiplicity
import Brockian.PentagonTraceBridge
import Brockian.D5CharacterComplete
import Brockian.CycleSpectrumFamily
import Brockian.GaloisCyclicGroup
import Brockian.GaloisWhyFive
import Brockian.GaloisGeneralDegree
import Brockian.GaloisNgonClassification
import Brockian.GaloisMinPolyFamily
import Brockian.GoldenSpectralCharacterization
import Brockian.GoldenDivisibility
import Brockian.PentagonGrandEquivalence
import Brockian.D5RateBlocks
import Brockian.D5EquivariantOperators
import Brockian.D5Commutant
import Brockian.D5MarkovContraction
import Brockian.D5RateComparison

/-!
# Focused D₅ research target

Build this module to check the pentagon action, Fourier and golden/cyclotomic
chain together with the equivariant-operator classification and commuting
rate comparison. The aggregate deliberately selects the D₅ dependency
closure rather than the repository's unrelated mathematical developments.

```
lake build Brockian.D5Research
lake env lean -DautoImplicit=false scripts/d5_axiom_audit.lean
```

See `D5_RESEARCH.md` for the exact statement boundaries,
reproduction environment, attribution, and source provenance.
-/
