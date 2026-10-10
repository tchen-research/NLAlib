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
