import NLAlib.Estimation.SLQAnalytic
import NLAlib.Estimation.SLQAnalyticSteps
import NLAlib.Estimation.SLQLipschitz
import NLAlib.Estimation.SLQPositiveLowerBound
import NLAlib.Estimation.SLQRademacher
import NLAlib.Estimation.HutchinsonLaws
import NLAlib.Estimation.Hutchinson
import NLAlib.Estimation.HutchinsonTail
import NLAlib.Estimation.Diagonal
import NLAlib.Estimation.Unbiased
import NLAlib.Estimation.SLQ

/-!
# Trace, diagonal and quadratic-form estimation

Layer 4 (`quadForm` is `NLAlib.Matrix.QuadForm`; Hanson–Wright is `NLAlib.Concentration.HansonWright`).
Files (atlas ids): `Hutchinson`, `HutchinsonLaws` (`hutchinson-unbiased`, `hutchinson-variance`),
`HutchinsonTail` (`hutchinson-tail`), `Diagonal` (`diagonal-estimator`), `Unbiased`
(`hutchpp-unbiased`, `xtrace-unbiased`, the expectation clause of `spectral-measure`), `SLQ`
(`slq-error`, case `f = 1/x`).
-/
