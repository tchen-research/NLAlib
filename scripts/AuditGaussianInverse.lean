import NLAlib.Gaussian.InverseMoments.SpectralTail

/-!
# Required completion audit for the four operator rederivations

This audit fails if any of the four requested declarations depends on sorryAx
or an axiom other than Lean's three standard classical axioms. Merely compiling
a theorem against a scaffold does not satisfy this task.
-/

open Lean Elab Command

set_option maxHeartbeats 0

run_cmd do
  let targets : List Name := [
    ``NLAlib.gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral,
    ``NLAlib.gaussianMatrix_lt_specNorm_pinvR_le,
    ``NLAlib.integrable_and_integral_specNorm_pinvR_gaussianMatrix_le,
    ``NLAlib.integrable_and_integral_specNorm_inv_self_mul_transpose_pow_gaussianMatrix_le,
    ``NLAlib.integrable_and_integral_rpow_specNorm_inv_gaussianMatrix_le_sharp,
    ``NLAlib.integral_rpow_specNorm_inv_gaussianMatrix_rpow_inv_le_sharp,
    ``NLAlib.integrable_and_integral_specNorm_pinvR_gaussianMatrix_le_sharp]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for d in targets do
    let axs ← collectAxioms d
    let extra := axs.filter (fun a => !allowed.contains a)
    if extra.isEmpty then
      logInfo m!"PASS {d}: {axs}"
    else
      logError m!"INCOMPLETE {d}: {extra}"

run_cmd do
  let env ← getEnv
  let forbidden : List Name := [
    `NLAlib.nonneg_of_tendsto_integral_of_uniform_lower_bound,
    `NLAlib.integral_nonneg_of_shift_identity_limit,
    `NLAlib.integral_nonneg_of_positive_translates,
    `NLAlib.integral_nonneg_of_gaussian_coordinate_approximation,
    `NLAlib.ae_exists_tendsto_gramSoftMinLaplacian_le_gaussianMatrix,
    `NLAlib.integral_sigmaMin_transpose_sq_law_weak_nonneg_gaussianMatrix,
    `NLAlib.integral_sigmaMin_transpose_sq_weak_nonneg_gaussianMatrix]
  let mut pending : List Name := [
    ``NLAlib.gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral,
    ``NLAlib.gaussianMatrix_lt_specNorm_pinvR_le]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if !seen.contains name then
      seen := seen.insert name
      if forbidden.contains name then
        logError m!"Old regularization/Fatou dependency remains: {name}"
      if name.toString.startsWith "NLAlib." || name.toString.startsWith "_private.NLAlib." then
        if let some ci := env.find? name then
          pending := ci.type.getUsedConstants.toList ++ pending
          match ci with
          | .thmInfo info => pending := info.value.getUsedConstants.toList ++ pending
          | .defnInfo info => pending := info.value.getUsedConstants.toList ++ pending
          | .opaqueInfo info => pending := info.value.getUsedConstants.toList ++ pending
          | _ => pure ()
  logInfo m!"Checked {seen.size} transitive constants for the unshifted tail route."
