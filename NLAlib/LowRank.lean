import NLAlib.LowRank.CholeskyHistories
import NLAlib.LowRank.CholeskyPivot
import NLAlib.LowRank.ComplexCholeskyHistories
import NLAlib.LowRank.ComplexCholeskyPivot
import NLAlib.LowRank.ComplexPolynomialFilter
import NLAlib.LowRank.ComplexPolynomialFilterBounds
import NLAlib.LowRank.ComplexRandomPivotedCholesky
import NLAlib.LowRank.ComplexSubspaceAngles
import NLAlib.LowRank.ComplexSubspaceConvergence
import NLAlib.LowRank.ComplexVolumeSampling
import NLAlib.LowRank.ComplexVolumeSamplingEndpoints
import NLAlib.LowRank.ComplexVolumeSamplingError
import NLAlib.LowRank.ComplexVolumeSamplingLaw
import NLAlib.LowRank.ExpectedPower
import NLAlib.LowRank.GaussianSpectralEndpoints
import NLAlib.LowRank.PolynomialFilter
import NLAlib.LowRank.RandomPivotedCholesky
import NLAlib.LowRank.RandomStartEndpoints
import NLAlib.LowRank.RandomStartLanczos
import NLAlib.LowRank.RandomStartPower
import NLAlib.LowRank.SubspaceConvergence
import NLAlib.LowRank.TraceDrift
import NLAlib.LowRank.TracePotential
import NLAlib.LowRank.VolumeCounting
import NLAlib.LowRank.VolumeSampling
import NLAlib.LowRank.GaussianNystrom
import NLAlib.LowRank.OptimalError
import NLAlib.LowRank.RawGaussianNystrom
import NLAlib.LowRank.RawNystromBridge
import NLAlib.LowRank.Basic
import NLAlib.LowRank.RangeFinder
import NLAlib.LowRank.GeneralizedNystrom
import NLAlib.LowRank.GaussianSketch
import NLAlib.LowRank.RSVD
import NLAlib.LowRank.Assembly
import NLAlib.LowRank.SketchedRegression
import NLAlib.LowRank.SpectralRangeFinder
import NLAlib.LowRank.PowerIteration
import NLAlib.LowRank.Nystrom

/-!
# Low-rank approximation

Layer 4: imports `Matrix`, `Concentration`, `Gaussian`, `Sketching`.

* `RangeFinder`: the deterministic range-finder bound (HMT 2011, Thm 9.1, Frobenius form), its
  truncated variant and the singular-value tail bound (atlas `hmt-9-1-frobenius`,
  `sigma-tail-bound`);
* `SpectralRangeFinder`: the spectral form of HMT 2011, Thm 9.1 (atlas `hmt-9-1-spectral`);
* `PowerIteration`: HMT 2011, Prop 8.6 and Thm 9.2 (atlas `power-iteration-deterministic`);
* `Nystrom`: the Nyström structural identity and the Gaussian expected trace error
  (atlas `nystrom-structural`, `nystrom-randomized`);
* `SketchedRegression`: the deterministic identities of the sketched core fit
  (atlas `sketched-regression`);
* `Assembly`: expectation-level arithmetic of the RSVD and generalized Nyström bounds;
* `RSVD`, `GeneralizedNystrom`: the expected-error bounds with the Gaussian facts as hypotheses
  (atlas `rsvd-expected-error`, `gn-expected-error`);
* `GaussianSketch`: the same bounds with standard Gaussian test matrices, no Gaussian hypothesis.
-/
