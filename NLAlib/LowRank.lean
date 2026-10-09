import NLAlib.LowRank.Basic
import NLAlib.LowRank.RangeFinder
import NLAlib.LowRank.GeneralizedNystrom
import NLAlib.LowRank.GaussianSketch
import NLAlib.LowRank.RSVD
import NLAlib.LowRank.Assembly
import NLAlib.LowRank.SketchedRegression

/-!
# Low-rank approximation

Layer 4: imports `Matrix`, `Concentration`, `Gaussian`, `Sketching`.

* `RangeFinder`: the deterministic range-finder bound (HMT 2011, Thm 9.1, Frobenius form), its
  truncated variant and the singular-value tail bound (atlas `hmt-9-1-frobenius`,
  `sigma-tail-bound`);
* `SketchedRegression`: the deterministic identities of the sketched core fit
  (atlas `sketched-regression`);
* `Assembly`: expectation-level arithmetic of the RSVD and generalized Nyström bounds;
* `RSVD`, `GeneralizedNystrom`: the expected-error bounds with the Gaussian facts as hypotheses
  (atlas `rsvd-expected-error`, `gn-expected-error`);
* `GaussianSketch`: the same bounds with standard Gaussian test matrices, no Gaussian hypothesis.
-/
