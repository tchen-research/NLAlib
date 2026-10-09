import NLAlib.Concentration.Matrix.Bernstein.BernsteinMgfCgf
import NLAlib.Concentration.Matrix.Bernstein.DilationIdentities
import NLAlib.Concentration.Matrix.Bernstein.DilationVariance
import NLAlib.Concentration.Matrix.Bernstein.HermitianBernstein
import NLAlib.Concentration.Matrix.Bernstein.IndependentSumSecondMoment
import NLAlib.Concentration.Matrix.Bernstein.MatrixBernstein
import NLAlib.Concentration.Matrix.Bernstein.VarianceAdditivity
import NLAlib.Concentration.Matrix.Chernoff.ChernoffMgfCgf
import NLAlib.Concentration.Matrix.Chernoff.MatrixChernoff
import NLAlib.Concentration.Matrix.Defs.Ch4ScalarLaws
import NLAlib.Concentration.Matrix.Defs.Ch5ChernoffFunctions
import NLAlib.Concentration.Matrix.Defs.Ch7Intrinsic
import NLAlib.Concentration.Matrix.Defs.Ch8Entropy
import NLAlib.Concentration.Matrix.Defs.Ch8JointTensor
import NLAlib.Concentration.Matrix.Defs.Dilation
import NLAlib.Concentration.Matrix.Defs.Probability
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

Tropp, *An Introduction to Matrix Concentration Inequalities* (2015), Chapters 3–8: the matrix Laplace
transform method (Laplace/), Gaussian and Rademacher series (Series/), matrix Chernoff (Chernoff/),
matrix Bernstein (Bernstein/), intrinsic dimension (Intrinsic/), and Lieb's concavity theorem with the
operator-convexity toolkit (OperatorConvexity/). Shared definitions in Defs/. Every theorem is proved.
-/
