import NLAlib.ForMathlib.LinearAlgebra.MatrixBicommutant
import NLAlib.ForMathlib.Algebra.NewtonCayley
import NLAlib.Matrix.Spectral.MatrixPowerConvergence
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Matrix Newton iteration in Cayley coordinates

Inverse-closed commutative bicommutants transfer the scalar rational
identity to arbitrary matrices. Power convergence certifies every
denominator, without normality. Higham, Functions of Matrices, Chapter 5.
-/

noncomputable section
open Matrix Filter
open scoped Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The inverse Cayley value for a total matrix argument. -/
def inverseCayley (T : Matrix n n ℂ) : Matrix n n ℂ := (1-T)⁻¹*(1+T)

/-- Newton averaging of an inverse Cayley value squares its coordinate,
provided both original denominators are invertible. -/
theorem half_smul_inverseCayley_add_inv (T : Matrix n n ℂ)
    (hm : IsUnit (1-T)) (hp : IsUnit (1+T)) :
    (2 : ℂ)⁻¹ • (inverseCayley T + (inverseCayley T)⁻¹) = inverseCayley (T^2) := by
  let R := bicommutantAlgebra T
  let t : R := ⟨T, self_mem_bicommutantAlgebra T⟩
  let d : R := bicommutantInverse (1-t)
  let e : R := bicommutantInverse (1+t)
  let c : R := algebraMap ℂ R ((2 : ℂ)⁻¹)
  have hd : (1-t)*d=1 := Subtype.ext (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hm))
  have he : (1+t)*e=1 := Subtype.ext (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hp))
  have hc : c*2=1 := by
    change algebraMap ℂ R ((2 : ℂ)⁻¹) * algebraMap ℂ R 2 = 1
    rw [← map_mul]
    norm_num
  have hxi : (inverseCayley T)⁻¹ = (e*(1-t) : R).val := by
    apply Matrix.inv_eq_right_inv
    exact congrArg Subtype.val (CommRing.cayley_value_mul_inverse t d e hd he)
  have hdi : (1-T^2)⁻¹ = (d*e : R).val := by
    apply Matrix.inv_eq_right_inv
    exact congrArg Subtype.val (CommRing.one_sub_sq_mul_inverse_product t d e hd he)
  have hh := congrArg Subtype.val (CommRing.half_mul_cayley_add_inverse t d e c hd he hc)
  rw [hxi]
  change (2 : ℂ)⁻¹ • ((1-T)⁻¹*(1+T)+(e*(1-t) : R).val) = (1-T^2)⁻¹*(1+T^2)
  rw [hdi]
  simpa [c, d, e, t, bicommutantInverse, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mul] using hh

/-- Power convergence also holds for the negative matrix. -/
theorem tendsto_neg_matrix_pow_zero {T : Matrix n n ℂ}
    (h : Tendsto (fun k : ℕ => T^k) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => (-T)^k) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at h ⊢
  have he (k : ℕ) : ‖(-T)^k‖=‖T^k‖ := by
    by_cases hk : Even k
    · rw [hk.neg_pow]
    · rw [(Nat.not_even_iff_odd.mp hk).neg_pow, norm_neg]
  simpa only [he] using h

/-- Every positive power of a matrix with convergent powers has both
unit Cayley denominators. -/
theorem isUnit_one_sub_and_add_matrix_pow {T : Matrix n n ℂ}
    (h : Tendsto (fun k : ℕ => T^k) atTop (𝓝 0)) {m : ℕ} (hm : 0 < m) :
    IsUnit (1-T^m) ∧ IsUnit (1+T^m) := by
  have hp : Tendsto (fun k : ℕ => (T^m)^k) atTop (𝓝 0) := by
    have ht : Tendsto (fun k : ℕ => m*k) atTop atTop := by
      simpa using (tendsto_id.nsmul_atTop hm : Tendsto (fun k : ℕ => m • k) atTop atTop)
    simpa only [Function.comp_def, pow_mul] using h.comp ht
  constructor
  · exact isUnit_one_sub_of_matrix_spectralRadius_lt_one
      (spectralRadius_lt_one_of_tendsto_matrix_pow_zero hp)
  · simpa only [sub_neg_eq_add] using isUnit_one_sub_of_matrix_spectralRadius_lt_one
      (spectralRadius_lt_one_of_tendsto_matrix_pow_zero (tendsto_neg_matrix_pow_zero hp))

/-- Inverse Cayley values are nonsingular if both denominators are units. -/
theorem isUnit_inverseCayley {T : Matrix n n ℂ}
    (hm : IsUnit (1-T)) (hp : IsUnit (1+T)) : IsUnit (inverseCayley T) := by
  exact (Matrix.isUnit_nonsing_inv_iff.mpr hm).mul hp

end NLAlib
