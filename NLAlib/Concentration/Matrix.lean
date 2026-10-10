import NLAlib.Concentration.Matrix.Bernstein.BernsteinMgfCgf
import NLAlib.Concentration.Matrix.Bernstein.DilationIdentities
import NLAlib.Concentration.Matrix.Bernstein.DilationVariance
import NLAlib.Concentration.Matrix.Bernstein.HermitianBernstein
import NLAlib.Concentration.Matrix.Bernstein.IndependentSumSecondMoment
import NLAlib.Concentration.Matrix.Bernstein.MatrixBernstein
import NLAlib.Concentration.Matrix.Bernstein.VarianceAdditivity
import NLAlib.Concentration.Matrix.Chernoff.ChernoffMgfCgf
import NLAlib.Concentration.Matrix.Chernoff.MatrixChernoff
import NLAlib.Concentration.Matrix.Sampling
import NLAlib.Concentration.Matrix.Defs.Calculus
import NLAlib.Concentration.Matrix.Defs.ChernoffFunctions
import NLAlib.Concentration.Matrix.Defs.Dilation
import NLAlib.Concentration.Matrix.Defs.IntrinsicDimension
import NLAlib.Concentration.Matrix.Defs.JointTensor
import NLAlib.Concentration.Matrix.Defs.Probability
import NLAlib.Concentration.Matrix.Defs.RelativeEntropy
import NLAlib.Concentration.Matrix.Defs.ScalarLaws
import NLAlib.Concentration.Matrix.Defs.Spectral
import NLAlib.Concentration.Matrix.Intrinsic.BlockIntrinsic
import NLAlib.Concentration.Matrix.Intrinsic.GeneralizedLaplace
import NLAlib.Concentration.Matrix.Intrinsic.IntrinsicBernsteinExpectation
import NLAlib.Concentration.Matrix.Intrinsic.IntrinsicBernstein
import NLAlib.Concentration.Matrix.Intrinsic.IntrinsicChernoff
import NLAlib.Concentration.Matrix.Intrinsic.IntrinsicDimension
import NLAlib.Concentration.Matrix.Intrinsic.IntrinsicHermitianBernstein
import NLAlib.Concentration.Matrix.Laplace.CgfExpLog
import NLAlib.Concentration.Matrix.Laplace.CgfIndependentReplacement
import NLAlib.Concentration.Matrix.Laplace.ExpectExtremaIntegrable
import NLAlib.Concentration.Matrix.Laplace.LaplaceExpectations
import NLAlib.Concentration.Matrix.Laplace.LaplaceTails
import NLAlib.Concentration.Matrix.Laplace.LiebIntegralPosDef
import NLAlib.Concentration.Matrix.Laplace.LiebJensen
import NLAlib.Concentration.Matrix.Laplace.LiebRegularityShiftIntegrable
import NLAlib.Concentration.Matrix.Laplace.MasterBounds
import NLAlib.Concentration.Matrix.Laplace.MasterSumExponentialIntegrable
import NLAlib.Concentration.Matrix.Laplace.ProbabilisticLieb
import NLAlib.Concentration.Matrix.Laplace.TailSpectralComparison
import NLAlib.Concentration.Matrix.Laplace.TraceCgfSubadditivity
import NLAlib.Concentration.Matrix.OperatorConvexity.EntropyJointConvex
import NLAlib.Concentration.Matrix.OperatorConvexity.EntropyNonnegative
import NLAlib.Concentration.Matrix.OperatorConvexity.GeneralizedKlein
import NLAlib.Concentration.Matrix.OperatorConvexity.JensenBlockCalculus
import NLAlib.Concentration.Matrix.OperatorConvexity.JensenIsometricCompression
import NLAlib.Concentration.Matrix.OperatorConvexity.JensenReflectionAlgebra
import NLAlib.Concentration.Matrix.OperatorConvexity.JointTensorRepresentation
import NLAlib.Concentration.Matrix.OperatorConvexity.LiebConcavity
import NLAlib.Concentration.Matrix.OperatorConvexity.LogOperatorConcave
import NLAlib.Concentration.Matrix.OperatorConvexity.LogOperatorMonotone
import NLAlib.Concentration.Matrix.OperatorConvexity.OperatorJensen
import NLAlib.Concentration.Matrix.OperatorConvexity.PerspectiveConvex
import NLAlib.Concentration.Matrix.OperatorConvexity.PerspectiveSqrtNormalization
import NLAlib.Concentration.Matrix.OperatorConvexity.TraceExpMonotone
import NLAlib.Concentration.Matrix.OperatorConvexity.VariationalTraceExp
import NLAlib.Concentration.Matrix.OperatorConvexity.VariationalTrace
import NLAlib.Concentration.Matrix.Series.GaussianMgfCgf
import NLAlib.Concentration.Matrix.Series.HermitianSeries
import NLAlib.Concentration.Matrix.Series.MatrixSeries
import NLAlib.Concentration.Matrix.Series.RademacherMgfCgf

/-!
# Matrix concentration inequalities

Tropp, *An Introduction to Matrix Concentration Inequalities* (2015), Chapters 3–8, ported from the
Prove2me missions for those chapters. Every theorem is proved.

| Directory | Contents | Atlas ids |
|---|---|---|
| `Defs/` | shared definitions (`spectralNorm`, `lambdaMax`, `matrixExp`, `LoewnerLE`, `dilation`, …) | `loewner-order`, `hermitian-dilation` |
| `Laplace/` | matrix Laplace transform method, `master_bounds`, `trace_cgf_subadditivity` | `matrix-laplace` |
| `Series/` | `hermitian_gaussian_series`, `matrix_gaussian_series` | `matrix-gaussian-series` |
| `Chernoff/` | `matrix_chernoff` | `matrix-chernoff` |
| `Sampling` | `matrix_chernoff_sampling` (explicit-constant tails for averages with `𝔼 Mₖ = I`) | `matrix-chernoff-sampling` |
| `Bernstein/` | `hermitian_bernstein`, `matrix_bernstein`, dilation identities | `matrix-bernstein`, `hermitian-dilation` |
| `Intrinsic/` | intrinsic-dimension Chernoff and Bernstein inequalities | `intrinsic-dimension` |
| `OperatorConvexity/` | `lieb_concavity`, `operator_jensen`, `matrixLog_le_matrixLog`, … | `operator-monotone-convex`, `loewner-order` |

`Defs/` modules: `Spectral` (spectral vocabulary, Loewner order), `Dilation`, `Probability` (Borel
instance, variance statistics, `cumulantSum`, `bernsteinTail`), `ScalarLaws` (Gaussian and
Rademacher laws, `gaussianSeriesTail`), `ChernoffFunctions`, `IntrinsicDimension`,
`RelativeEntropy` (matrix functions, relative entropy, operator convexity, perspective),
`JointTensor`, and `Calculus` (shared lemmas: spectral calculus of `matrixExp`/`traceExp`,
reindexing, dilation and block-diagonal integrals).

`golden-thompson` is not realised here: Tropp's route goes through Lieb's concavity theorem.
-/
