import NLAlib.Matrix.Gram
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
* `Gram`: `det ≠ 0` from full rank, positivity of `(G Gᵀ)⁻¹` and the entry bound
  `|Mᵢⱼ| ≤ Mᵢᵢ + Mⱼⱼ` for positive semidefinite `M`;
* `SVD`: `singularValues`, `IsSVD`, existence of the SVD;
* `Spectral`: `lamMin`, `sigmaMin`, their Lipschitz bounds, `‖(A Aᵀ)⁻¹‖₂ = 1/σ_min(Aᵀ)²`;
* `Measurable`: entrywise measurability of matrix-valued maps (Borel structure only).

Planned files (atlas ids): `EckartYoung` (`eckart-young`), `Weyl`
(`weyl-mirsky`), `CourantFischer` (`courant-fischer`), `Trace` (`von-neumann-trace`).
-/
