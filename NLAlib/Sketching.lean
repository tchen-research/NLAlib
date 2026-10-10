import NLAlib.Sketching.FiniteIndexTransport
import NLAlib.Sketching.Gram
import NLAlib.Sketching.SingularValueEmbedding
import NLAlib.Sketching.Basic
import NLAlib.Sketching.SubspaceEmbedding
import NLAlib.Sketching.JL
import NLAlib.Sketching.SubGaussianJL
import NLAlib.Sketching.Leverage
import NLAlib.Sketching.GaussianEmbedding
import NLAlib.Sketching.ApproxMultiplication

/-!
# Sketching primitives

Layer 3: imports `NLAlib.Matrix`, `NLAlib.Concentration`, `NLAlib.Gaussian`.

Files (atlas ids): `Basic` (`IsSubspaceEmbedding`), `SubspaceEmbedding` (`ose-def`), `JL`
(`jl-distributional`, `jl-lemma`), `Leverage` (`leverage-scores`), `GaussianEmbedding`
(`gaussian-ose`), `ApproxMultiplication` (`amm-ose`).
`SubGaussianJL` proves the independent-entry distributional theorem with an explicit
MGF constant and its independent-isotropic-row extension (`jl-subgaussian`).

Planned: `leverage-sampling-ose`, `amm-sampling`.
-/
