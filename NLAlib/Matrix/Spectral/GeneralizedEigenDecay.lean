import NLAlib.Matrix.Spectral.PrimaryTriangularization
import NLAlib.Matrix.Spectral.MatrixPowerConvergence

/-!
# Decay inside generalized eigenspaces of subunit eigenvalues

Restriction to a primary space has just one possible eigenvalue. Matrix
coordinates transfer the spectral-radius power-decay theorem to that space.
Source: Horn–Johnson (2013), §5.6.
-/

noncomputable section
open Module Filter
open scoped Matrix Topology

namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- A generalized eigenvector with eigenvalue of modulus below one has a
power orbit tending to zero. Source: Horn–Johnson (2013), Theorem 5.6.12;
the proof transfers matrix power decay to the restricted primary space. -/
theorem tendsto_pow_apply_zero_of_mem_maxGenEigenspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (f : Module.End ℂ E) {μ : ℂ} (hμ : ‖μ‖ < 1) {x : E}
    (hx : x ∈ f.maxGenEigenspace μ) : Tendsto (fun k : ℕ => (f ^ k) x) atTop (𝓝 0) := by
  let W := f.maxGenEigenspace μ
  have hpres : Set.MapsTo f W W := Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ
  let g : Module.End ℂ W := f.restrict hpres
  let b := Module.finBasis ℂ W
  let M := g.toMatrix b b
  have hspec (ν : ℂ) (hν : ν ∈ spectrum ℂ M) : ν = μ := by
    apply eq_of_hasEigenvalue_restrict_maxGenEigenspace f μ hpres
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hν
    simpa only [M, LinearMap.charpoly_toMatrix] using hroot
  have hρ : spectralRadius ℂ M < 1 := by
    have hle : spectralRadius ℂ M ≤ (‖μ‖₊ : ENNReal) := by
      apply iSup₂_le
      intro ν hν
      rw [hspec ν hν]
    exact hle.trans_lt (by exact_mod_cast hμ)
  let L : Matrix (Fin (finrank ℂ W)) (Fin (finrank ℂ W)) ℂ →ₗ[ℂ] (W →L[ℂ] W) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp (Matrix.toLin b b).toLinearMap
  have hLpow (k : ℕ) : L (M ^ k) = (LinearMap.toContinuousLinearMap (g ^ k)) := by
    change LinearMap.toContinuousLinearMap (Matrix.toLin b b (M ^ k)) = _
    rw [Matrix.toLin_pow, show Matrix.toLin b b M = g from Matrix.toLin_toMatrix b b g]
  have hL : Tendsto (fun k : ℕ => L (M ^ k)) atTop (𝓝 0) := by
    have h := L.continuous_of_finiteDimensional.continuousAt.tendsto.comp
      (tendsto_matrix_pow_zero_of_spectralRadius_lt_one hρ)
    simpa only [map_zero, Function.comp_def] using h
  let z : W := ⟨x, hx⟩
  have hz : Tendsto (fun k : ℕ => (L (M ^ k)) z) atTop (𝓝 0) := by
    have hEval : Continuous (fun T : W →L[ℂ] W => T z) := by fun_prop
    simpa only [Function.comp_def, zero_apply] using hEval.continuousAt.tendsto.comp hL
  have hback (k : ℕ) : ((g ^ k) z : E) = (f ^ k) x := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      change f ((g ^ k) z : E) = f ((f ^ k) x)
      rw [ih]
  have h := W.subtypeL.continuous.continuousAt.tendsto.comp hz
  simpa only [Function.comp_def, hLpow, LinearMap.coe_toContinuousLinearMap',
    Submodule.coe_subtypeL, Submodule.subtype_apply, hback, map_zero] using h

end NLAlib
