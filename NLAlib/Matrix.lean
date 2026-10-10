import NLAlib.Matrix.CoordinateUpdates
import NLAlib.Matrix.CoordinatePinching
import NLAlib.Matrix.CourantFischer
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
import NLAlib.Matrix.PolynomialCalculus
import NLAlib.Matrix.QuadraticProbe
import NLAlib.Matrix.RankNorm
import NLAlib.Matrix.RayleighNorm
import NLAlib.Matrix.SpectralBounds
import NLAlib.Matrix.SpectralContinuity
import NLAlib.Matrix.SpectralMinimum
import NLAlib.Matrix.SvdBlocks
import NLAlib.Matrix.UnshiftedGramSoftMin
import NLAlib.Matrix.VonNeumann
import NLAlib.Matrix.Weyl
import NLAlib.Matrix.Gram
import NLAlib.Matrix.Measurable
import NLAlib.Matrix.Norms
import NLAlib.Matrix.Projections
import NLAlib.Matrix.Pseudoinverse
import NLAlib.Matrix.SVD
import NLAlib.Matrix.Spectral
import NLAlib.Matrix.QuadForm

/-!
# Matrix analysis toolkit

Deterministic facts every NLAlib proof reaches for. Layer 0 of the library: nothing here may
import probability.

* `Norms`: `frobInner`, `frobSq`, `frobNorm`, `specNorm` and their inequalities;
* `Projections`: `HasOrthonormalCols`, `residual`, `IsBestRankApprox`, projector identities,
  orthogonal completions;
* `Pseudoinverse`: the full-rank formulas `pinvL`, `pinvR`;
* `MoorePenrose`: the general inverse, uniqueness, Penrose identities and range projectors;
* `EckartYoung`: the attained Frobenius best-rank optimum, the truncated SVD and the spectral
  attainment `‖A − A_k‖₂ = σ_k`;
* `CourantFischer`: min-max for eigenvalues and singular values, attaining subspaces, Loewner
  monotonicity, eigenvalue Weyl inequality, Cauchy/Poincaré interlacing;
* `Weyl`: `σ_{i+j}(A+B) ≤ σ_i(A) + σ_j(B)`, `|σ_k(A+E) − σ_k(A)| ≤ ‖E‖₂`, Mirsky, products,
  and the spectral Eckart–Young theorem;
* `VonNeumann`: the von Neumann trace inequality and its rank corollary;
* `PolynomialCalculus`: `p(A) = U diag(p(λ)) Uᵀ` and the polynomial spectral bounds;
* `CoordinatePinching`: finite sign-reflection averaging and its diagonal endpoint;
* `RankNorm`, `FiniteIndexTransport`: rank-based norm bounds and arbitrary finite-index APIs;
* `Gram`: `det ≠ 0` from full rank, positivity of `(G Gᵀ)⁻¹` and the entry bound
  `|Mᵢⱼ| ≤ Mᵢᵢ + Mⱼⱼ` for positive semidefinite `M`;
* `SVD`: `singularValues`, `IsSVD`, existence of the SVD;
* `Spectral`: `lamMin`, `sigmaMin`, their Lipschitz bounds, `‖(A Aᵀ)⁻¹‖₂ = 1/σ_min(Aᵀ)²`;
* `Measurable`: entrywise measurability of matrix-valued maps (Borel structure only).
-/
