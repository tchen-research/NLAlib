import NLAlib.ForMathlib.Analysis.Calculus.CompactTestSupport
import NLAlib.ForMathlib.Analysis.DerivativeLimit
import NLAlib.ForMathlib.MeasureTheory.IntegralConvergence
import NLAlib.ForMathlib.MeasureTheory.LocalWeakDensity
import NLAlib.ForMathlib.MeasureTheory.MomentInterpolation
import NLAlib.ForMathlib.MeasureTheory.MonotoneDensity
import NLAlib.ForMathlib.MeasureTheory.SmoothMeasureComparison
import NLAlib.ForMathlib.MeasureTheory.WeakDensity
import NLAlib.ForMathlib.MeasureTheory.WeightedWeakDensity
import NLAlib.ForMathlib.Analysis.Real
import NLAlib.ForMathlib.Analysis.Calculus.MeanValue
import NLAlib.ForMathlib.MeasureTheory.Integral

/-!
# ForMathlib

Layer −1: general facts that are not about NLAlib's objects and are candidates for upstreaming
to Mathlib. Each file is named after the Mathlib directory it would land in.

* `Analysis/Real`: elementary inequalities for `√`, `log`, `exp`;
* `Analysis/Calculus/MeanValue`: linear growth from a bounded derivative;
* `MeasureTheory/Integral`: resampling one coordinate of a product measure, Cauchy–Schwarz,
  integrability under linear growth.
-/
