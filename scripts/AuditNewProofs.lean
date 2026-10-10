import NLAlib
open Lean Elab Command

/-! Audit all public and private theorem declarations in the new and completed
modules. None may depend on a scaffold or a nonstandard axiom. Existing JL
scaffolds remain outside these modules and are checked by scripts/Audit.lean. -/

run_cmd do
  let env ← getEnv
  let selected : List Name := [
    `NLAlib.Concentration.EntropyNonnegative,
    `NLAlib.Concentration.HansonWright.CenteredSquareBounds,
    `NLAlib.Concentration.HansonWright.Centering,
    `NLAlib.Concentration.HansonWright.CutAverages,
    `NLAlib.Concentration.HansonWright.Decoupling,
    `NLAlib.Concentration.HansonWright.DiagonalCGF,
    `NLAlib.Concentration.HansonWright.ExponentialSeries,
    `NLAlib.Concentration.HansonWright.GaussianProductIntegrability,
    `NLAlib.Concentration.HansonWright.Geometry,
    `NLAlib.Concentration.HansonWright.LinearFormComparison,
    `NLAlib.Concentration.HansonWright.ScalarMoments,
    `NLAlib.Concentration.HansonWright.TailAssembly,
    `NLAlib.Concentration.HansonWright.UniversalBound,
    `NLAlib.Concentration.HansonWright.VectorProductComparison,
    `NLAlib.Concentration.OrliczMGF,
    `NLAlib.Concentration.ScalarBernstein,
    `NLAlib.Estimation.HansonWright,
    `NLAlib.Estimation.HutchinsonLaws,
    `NLAlib.ForMathlib.Analysis.Calculus.CompactTestSupport,
    `NLAlib.ForMathlib.Analysis.DerivativeLimit,
    `NLAlib.ForMathlib.MeasureTheory.IntegralConvergence,
    `NLAlib.ForMathlib.MeasureTheory.LocalWeakDensity,
    `NLAlib.ForMathlib.MeasureTheory.MomentInterpolation,
    `NLAlib.ForMathlib.MeasureTheory.MonotoneDensity,
    `NLAlib.ForMathlib.MeasureTheory.SmoothMeasureComparison,
    `NLAlib.ForMathlib.MeasureTheory.WeakDensity,
    `NLAlib.ForMathlib.MeasureTheory.WeightedWeakDensity,
    `NLAlib.Gaussian.Concentration.IntegrationByParts,
    `NLAlib.Gaussian.Concentration.Stein,
    `NLAlib.Gaussian.InverseMoments,
    `NLAlib.Gaussian.InverseMoments.CutoffDerivativeIntegrability,
    `NLAlib.Gaussian.InverseMoments.CutoffIntegrability,
    `NLAlib.Gaussian.InverseMoments.GammaBounds,
    `NLAlib.Gaussian.InverseMoments.GaussianWeakInequality,
    `NLAlib.Gaussian.InverseMoments.HardEdgeEndpoint,
    `NLAlib.Gaussian.InverseMoments.LambdaMinTail,
    `NLAlib.Gaussian.InverseMoments.OperatorHardEdge,
    `NLAlib.Gaussian.InverseMoments.Probe,
    `NLAlib.Gaussian.InverseMoments.RegularizedApproximation,
    `NLAlib.Gaussian.InverseMoments.RegularizedIntegrability,
    `NLAlib.Gaussian.InverseMoments.ResolventLimit,
    `NLAlib.Gaussian.InverseMoments.SpectralProbe,
    `NLAlib.Gaussian.InverseMoments.SpectralTail,
    `NLAlib.Gaussian.InverseMoments.UnshiftedWeakInequality,
    `NLAlib.Gaussian.InverseMoments.WeakInequality,
    `NLAlib.Gaussian.LogSobolevCoverage,
    `NLAlib.Gaussian.LogSobolevHerbst,
    `NLAlib.Gaussian.OrnsteinUhlenbeckEntropyGrowth,
    `NLAlib.Gaussian.OrnsteinUhlenbeckGrowth,
    `NLAlib.Gaussian.PolynomialGrowth,
    `NLAlib.Gaussian.PolynomialGrowthIntegrationByParts,
    `NLAlib.Gaussian.PositiveMoments,
    `NLAlib.Gaussian.ProductIntegrationByParts,
    `NLAlib.Gaussian.SimpleSpectrum,
    `NLAlib.Gaussian.SketchRank,
    `NLAlib.Gaussian.SlepianTails,
    `NLAlib.LowRank.GaussianNystrom,
    `NLAlib.LowRank.OptimalError,
    `NLAlib.LowRank.RawGaussianNystrom,
    `NLAlib.LowRank.RawNystromBridge,
    `NLAlib.Matrix.CoordinateUpdates,
    `NLAlib.Matrix.EckartYoung,
    `NLAlib.Matrix.FiniteIndexTransport,
    `NLAlib.Matrix.GramCutoffCalculus,
    `NLAlib.Matrix.GramSoftMin,
    `NLAlib.Matrix.GramSoftMinMeasurable,
    `NLAlib.Matrix.GramSoftMinSpectral,
    `NLAlib.Matrix.GramTrace,
    `NLAlib.Matrix.InverseCalculus,
    `NLAlib.Matrix.InversePowerConcavity,
    `NLAlib.Matrix.InversePowerGrowth,
    `NLAlib.Matrix.InversePowerLaplacianLimit,
    `NLAlib.Matrix.InversePowerLimit,
    `NLAlib.Matrix.MoorePenrose,
    `NLAlib.Matrix.OptimalErrorContinuity,
    `NLAlib.Matrix.PolarFrame,
    `NLAlib.Matrix.QuadraticProbe,
    `NLAlib.Matrix.RankNorm,
    `NLAlib.Matrix.RayleighNorm,
    `NLAlib.Matrix.SpectralBounds,
    `NLAlib.Matrix.SpectralContinuity,
    `NLAlib.Matrix.SpectralMinimum,
    `NLAlib.Matrix.SvdBlocks,
    `NLAlib.Matrix.UnshiftedGramSoftMin,
    `NLAlib.Sketching.FiniteIndexTransport,
    `NLAlib.Sketching.Gram,
    `NLAlib.Sketching.SingularValueEmbedding,
    `NLAlib.Solvers.KaczmarzProbability]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut bad : Nat := 0
  for (name, ci) in env.constants.map₁.toList do
    if let .thmInfo _ := ci then
      if let some idx := env.getModuleIdxFor? name then
        let mod := env.header.moduleNames[idx.toNat]!
        if selected.contains mod then
          count := count + 1
          let axioms ← collectAxioms name
          if axioms.any (fun ax => !allowed.contains ax) then
            bad := bad + 1
            logError m!"{name} uses extra axioms: {axioms}"
  if bad == 0 then
    logInfo m!"PASS: {count} new/completed theorem declarations (including private helpers); only propext, Classical.choice, Quot.sound"
  else
    logError m!"FAIL: {bad} declarations depend on extra axioms"
