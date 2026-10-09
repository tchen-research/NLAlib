import NLAlib.Matrix.Measurable
import NLAlib.Matrix.Norms
import NLAlib.Matrix.Projections
import NLAlib.Matrix.Pseudoinverse
import NLAlib.Matrix.SVD
import NLAlib.Matrix.Spectral

/-!
# Matrix analysis toolkit

Deterministic facts every NLAlib proof reaches for. Layer 0 of the library: nothing here may
import probability.

* `Norms`: `frobInner`, `frobSq`, `frobNorm`, `specNorm` and their inequalities;
* `Projections`: `HasOrthonormalCols`, `residual`, `IsBestRankApprox`, projector identities,
  orthogonal completions;
* `Pseudoinverse`: `pinvL`, `pinvR` and the Penrose identities;
* `SVD`: `singularValues`, `IsSVD`, existence of the SVD;
* `Measurable`: entrywise measurability of matrix-valued maps (Borel structure only).

Planned files (atlas ids): `EckartYoung` (`eckart-young`), `Weyl`
(`weyl-mirsky`), `CourantFischer` (`courant-fischer`), `Trace` (`von-neumann-trace`).
-/
