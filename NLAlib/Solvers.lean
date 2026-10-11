import NLAlib.Solvers.KaczmarzProbability
import NLAlib.Solvers.Basic
import NLAlib.Solvers.Kaczmarz
import NLAlib.Solvers.KaczmarzExtensions
import NLAlib.Solvers.KaczmarzRowSpace
import NLAlib.Solvers.SketchProject

/-!
# Randomized solvers

Layer 5: may import everything.

* `Kaczmarz`: randomized Kaczmarz converges linearly in expectation (Strohmer–Vershynin 2009,
  Thm 2; atlas `randomized-kaczmarz`).
* `KaczmarzExtensions`: inconsistent systems (Needell 2010) and rank-deficient systems
  (Zouzias–Freris 2013); atlas `kaczmarz-inconsistent`, `kaczmarz-rank-deficient`.
* `SketchProject`: sketch-and-project (Gower–Richtárik 2015, Thm 4.6); atlas
  `sketch-and-project`.
* `KaczmarzRowSpace`: inconsistent-system bounds with coercivity and initial errors
  restricted to `range Aᵀ`, including the actual iid row-path expectation.
-/
