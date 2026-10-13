import Mathlib.Analysis.Convex.Integral
import NLAlib.ForMathlib.Analysis.Convex.Integral

/-!
# Jensen inequality on a nonclosed convex domain

Main declaration: `NLAlib.ConcaveOn.le_map_integral_of_integral_mem`.

Atlas: `matrix-laplace` (step of Corollary 3.4.2).

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Jensen inequality (2.2.2), printed p. 25, and its use in Corollary 3.4.2, printed p. 35. Auxiliary Banach-space formulation with explicit integrability, continuity, and mean-membership hypotheses.
-/
open MeasureTheory
open Set Filter
open scoped Topology

