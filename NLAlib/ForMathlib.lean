import NLAlib.ForMathlib.Algebra.DiagonalSums
import NLAlib.ForMathlib.Algebra.Intervals
import NLAlib.ForMathlib.Analysis.BernsteinParameter
import NLAlib.ForMathlib.Analysis.FourierCircle
import NLAlib.ForMathlib.Analysis.FourierConvolution
import NLAlib.ForMathlib.Analysis.GeometricRate
import NLAlib.ForMathlib.Analysis.InnerProductSpace.GramSchmidt
import NLAlib.ForMathlib.Analysis.Lipschitz
import NLAlib.ForMathlib.Analysis.LogPowerMean
import NLAlib.ForMathlib.Analysis.Matrix.Order
import NLAlib.ForMathlib.Analysis.Matrix.QuadraticForm
import NLAlib.ForMathlib.Analysis.PowerInequalities
import NLAlib.ForMathlib.MeasureTheory.ConditionalComparison
import NLAlib.ForMathlib.MeasureTheory.ConditionalJensen
import NLAlib.ForMathlib.MeasureTheory.ConditionalParameterJensen
import NLAlib.ForMathlib.MeasureTheory.MatrixConditionalExpectation
import NLAlib.ForMathlib.Probability.BoundedDifferences
import NLAlib.ForMathlib.Probability.ExponentialTailMoments
import NLAlib.ForMathlib.Probability.FiniteL2
import NLAlib.ForMathlib.Probability.FiniteLaw
import NLAlib.ForMathlib.Probability.FiniteLawBasics
import NLAlib.ForMathlib.Probability.FiniteLawIndependent
import NLAlib.ForMathlib.Probability.FiniteLawMeasure
import NLAlib.ForMathlib.Probability.FiniteProductEvents
import NLAlib.ForMathlib.Probability.FiniteProductLaw
import NLAlib.ForMathlib.Probability.NonnegativeSupermartingale
import NLAlib.ForMathlib.Probability.SampleAverage
import NLAlib.ForMathlib.Probability.UniformCollision
import NLAlib.ForMathlib.Probability.UniformProduct
import NLAlib.ForMathlib.Probability.UniformSamplingCounts
import NLAlib.ForMathlib.Probability.UniformSamplingCoupling
import NLAlib.ForMathlib.Probability.UniformSamplingJensen
import NLAlib.ForMathlib.Probability.UniformSamplingMarginals
import NLAlib.ForMathlib.Analysis.Calculus.CompactTestSupport
import NLAlib.ForMathlib.Analysis.DerivativeLimit
import NLAlib.ForMathlib.MeasureTheory.IntegralConvergence
import NLAlib.ForMathlib.MeasureTheory.LocalWeakDensity
import NLAlib.ForMathlib.MeasureTheory.MomentInterpolation
import NLAlib.ForMathlib.MeasureTheory.MonotoneDensity
import NLAlib.ForMathlib.MeasureTheory.SmoothMeasureComparison
import NLAlib.ForMathlib.MeasureTheory.WeakDensity
import NLAlib.ForMathlib.MeasureTheory.WeightedWeakDensity
import NLAlib.ForMathlib.Algebra.Polynomial
import NLAlib.ForMathlib.Analysis.Real
import NLAlib.ForMathlib.Analysis.Calculus.IteratedDeriv
import NLAlib.ForMathlib.Analysis.Calculus.MeanValue
import NLAlib.ForMathlib.MeasureTheory.Integral

/-!
# ForMathlib

Layer −1: general facts that are not about NLAlib's objects and are candidates for upstreaming
to Mathlib. Each file is named after the Mathlib directory it would land in.

* `Algebra/Polynomial`: degree under scalar multiplication, vanishing on an interval, the top
  derivative of a polynomial;
* `Analysis/Calculus/IteratedDeriv`: iterated derivatives of `f − p` for a polynomial `p`;
* `Analysis/Real`: elementary inequalities for `√`, `log`, `exp`;
* `Analysis/Calculus/MeanValue`: linear growth from a bounded derivative;
* `MeasureTheory/Integral`: resampling one coordinate of a product measure, Cauchy–Schwarz,
  integrability under linear growth.
-/
