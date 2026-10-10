import NLAlib.Matrix.CoordinateUpdates
import NLAlib.Matrix.EckartYoung
import NLAlib.Matrix.FiniteIndexTransport
import NLAlib.Matrix.GramCutoffCalculus
import NLAlib.Matrix.GramSoftMin
import NLAlib.Matrix.GramSoftMinMeasurable
import NLAlib.Matrix.GramSoftMinSpectral
import NLAlib.Matrix.GramTrace
import NLAlib.Matrix.InverseCalculus
import NLAlib.Matrix.InversePowerConcavity
import NLAlib.Matrix.InversePowerGrowth
import NLAlib.Matrix.InversePowerLaplacianLimit
import NLAlib.Matrix.InversePowerLimit
import NLAlib.Matrix.MoorePenrose
import NLAlib.Matrix.OptimalErrorContinuity
import NLAlib.Matrix.PolarFrame
import NLAlib.Matrix.QuadraticProbe
import NLAlib.Matrix.RankNorm
import NLAlib.Matrix.RayleighNorm
import NLAlib.Matrix.SpectralBounds
import NLAlib.Matrix.SpectralContinuity
import NLAlib.Matrix.SpectralMinimum
import NLAlib.Matrix.SvdBlocks
import NLAlib.Matrix.UnshiftedGramSoftMin
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
* `Pseudoinverse`: the full-rank formulas `pinvL`, `pinvR`;
* `MoorePenrose`: the general inverse, uniqueness, Penrose identities and range projectors;
* `EckartYoung`: the attained Frobenius best-rank optimum and the truncated SVD;
* `RankNorm`, `FiniteIndexTransport`: rank-based norm bounds and arbitrary finite-index APIs;
* `Gram`: `det ≠ 0` from full rank, positivity of `(G Gᵀ)⁻¹` and the entry bound
  `|Mᵢⱼ| ≤ Mᵢᵢ + Mⱼⱼ` for positive semidefinite `M`;
* `SVD`: `singularValues`, `IsSVD`, existence of the SVD;
* `Spectral`: `lamMin`, `sigmaMin`, their Lipschitz bounds, `‖(A Aᵀ)⁻¹‖₂ = 1/σ_min(Aᵀ)²`;
* `Measurable`: entrywise measurability of matrix-valued maps (Borel structure only).

Remaining spectral results (atlas ids): the spectral part of `EckartYoung` (`eckart-young`), `Weyl`
(`weyl-mirsky`), `CourantFischer` (`courant-fischer`), `Trace` (`von-neumann-trace`).
-/
