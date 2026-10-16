import NLAlib.Matrix.Spectral.MatrixPowerConvergence
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Hurwitz matrices and the stable Cayley transform

The fractional linear spectral map is obtained from the general algebraic
spectrum rules for a unit inverse, scalar scaling and translation. No normality
or diagonalizability is required.
-/

noncomputable section
open scoped Matrix Pointwise
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Every complex spectral point lies in the strict left half-plane. -/
def IsHurwitz (A : Matrix n n ℂ) : Prop := ∀ z ∈ spectrum ℂ A, z.re < 0

open scoped Matrix.Norms.L2Operator in
/-- Positive real shifts are outside the spectrum of a Hurwitz matrix. -/
theorem IsHurwitz.isUnit_sub_pos_smul_one {A : Matrix n n ℂ} (hA : IsHurwitz A)
    (p : ℝ) (hp : 0 < p) : IsUnit (A - (p : ℂ) • 1) := by
  have hnot : (p : ℂ) ∉ spectrum ℂ A := by
    intro h
    have := hA _ h
    simpa using (not_lt_of_ge hp.le this)
  have hu : IsUnit (algebraMap ℂ (Matrix n n ℂ) (p : ℂ) - A) :=
    not_not.mp (fun h => hnot h)
  simpa only [Algebra.algebraMap_eq_smul_one, neg_sub] using hu.neg

open scoped Matrix.Norms.L2Operator in
/-- The real positive-shift Cayley matrix. -/
def cayleyTransform {K : Type*} [RCLike K] (A : Matrix n n K) (p : ℝ) : Matrix n n K :=
  (A + (p : K) • 1) * (A - (p : K) • 1)⁻¹

open scoped Matrix.Norms.L2Operator in
/-- The Cayley matrix has its resolvent form whenever the solved denominator
is invertible. -/
theorem cayleyTransform_eq_one_add {K : Type*} [RCLike K] (A : Matrix n n K) (p : ℝ)
    (h : IsUnit (A - (p : K) • 1).det) :
    cayleyTransform A p = 1 + (2 * (p : K)) • (A - (p : K) • 1)⁻¹ := by
  have heq : A + (p : K) • (1 : Matrix n n K) =
      (A - (p : K) • 1) + (2 * (p : K)) • 1 := by module
  rw [cayleyTransform, heq, Matrix.add_mul, Matrix.mul_nonsing_inv _ h]
  simp

open scoped Matrix.Norms.L2Operator in
/-- The scalar Cayley quotient maps the strict left half-plane into the
open unit disk. -/
theorem norm_cayley_lt_one {z : ℂ} (hz : z.re < 0) (p : ℝ) (hp : 0 < p) :
    ‖(z + (p : ℂ)) / (z - (p : ℂ))‖ < 1 := by
  have hd : z - (p : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hr
    linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  have hs : ‖z + (p : ℂ)‖ ^ 2 < ‖z - (p : ℂ)‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_sub,
      Complex.normSq_ofReal, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  nlinarith [norm_nonneg (z + (p : ℂ)), norm_nonneg (z - (p : ℂ))]

open scoped Matrix.Norms.L2Operator in
/-- The actual Cayley spectrum is the image of the original spectrum under
its scalar fractional linear function. -/
theorem spectrum_cayleyTransform (A : Matrix n n ℂ) (p : ℝ) (hp : p ≠ 0)
    (h : IsUnit (A - (p : ℂ) • 1)) :
    spectrum ℂ (cayleyTransform A p) =
      (fun z : ℂ => (z + (p : ℂ)) / (z - (p : ℂ))) '' spectrum ℂ A := by
  let u := h.unit
  have huval : (u : Matrix n n ℂ) = A - (p : ℂ) • 1 := h.unit_spec
  have huinv : (A - (p : ℂ) • 1)⁻¹ = (↑u⁻¹ : Matrix n n ℂ) := by
    apply Matrix.inv_eq_right_inv
    rw [← huval]
    exact u.val_inv
  have hinv : spectrum ℂ (A - (p : ℂ) • 1)⁻¹ =
      (spectrum ℂ (A - (p : ℂ) • 1))⁻¹ := by
    rw [huinv, ← spectrum.map_inv u, huval]
  have hscale : (2 * (p : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast hp)
  have hshift : spectrum ℂ (A - (p : ℂ) • 1) = spectrum ℂ A - {(p : ℂ)} := by
    simpa only [Algebra.algebraMap_eq_smul_one] using (spectrum.sub_singleton_eq A (p : ℂ)).symm
  rw [cayleyTransform_eq_one_add A p ((Matrix.isUnit_iff_isUnit_det _).mp h)]
  change spectrum ℂ (algebraMap ℂ (Matrix n n ℂ) 1 +
    (Units.mk0 (2 * (p : ℂ)) hscale) • (A - (p : ℂ) • 1)⁻¹) = _
  rw [← spectrum.singleton_add_eq, spectrum.unit_smul_eq_smul _ (Units.mk0 _ hscale),
    hinv, hshift]
  have hden (z : ℂ) (hz : z ∈ spectrum ℂ A) : z - (p : ℂ) ≠ 0 := by
    have hm : z - (p : ℂ) ∈ spectrum ℂ (A - (p : ℂ) • 1) := by
      rw [hshift]
      exact ⟨z, hz, (p : ℂ), rfl, rfl⟩
    intro heq
    rw [heq] at hm
    exact spectrum.zero_notMem ℂ h hm
  ext w
  simp only [Set.mem_add, Set.mem_singleton_iff, Set.mem_smul_set, Set.mem_inv,
    Set.mem_sub, Set.mem_image]
  constructor
  · rintro ⟨_, rfl, v, ⟨v', ⟨z, hz, _, rfl, hzv⟩, hvinv⟩, hvw⟩
    refine ⟨z, hz, ?_⟩
    have hv' : v' = (z - (p : ℂ))⁻¹ := by
      simpa only [inv_inv] using (congrArg Inv.inv hzv).symm
    rw [← hvw, ← hvinv, hv']
    change (z + (p : ℂ)) / (z - (p : ℂ)) = 1 + (2 * (p : ℂ)) * (z - (p : ℂ))⁻¹
    field_simp [hden z hz]
    ring
  · rintro ⟨z, hz, rfl⟩
    refine ⟨1, rfl, (Units.mk0 (2 * (p : ℂ)) hscale) • (z - (p : ℂ))⁻¹, ?_, ?_⟩
    · exact ⟨(z - (p : ℂ))⁻¹, ⟨z, hz, (p : ℂ), rfl, by simp⟩, rfl⟩
    · change 1 + (2 * (p : ℂ)) * (z - (p : ℂ))⁻¹ = (z + (p : ℂ)) / (z - (p : ℂ))
      field_simp [hden z hz]
      ring

open scoped Matrix.Norms.L2Operator in
/-- Every fixed positive-shift Cayley transform of a Hurwitz matrix is
strictly discretely stable, including nonnormal and defective matrices.
Source: user derivations, Lyapunov ADI fixed-shift convergence.
atlas: lyapunov-adi-residual-factor (partial), lyapunov-stability-gramian (partial) -/
theorem IsHurwitz.spectralRadius_cayleyTransform_lt_one {A : Matrix n n ℂ}
    (hA : IsHurwitz A) (p : ℝ) (hp : 0 < p) : spectralRadius ℂ (cayleyTransform A p) < 1 := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have hz : cayleyTransform A p = 0 := Subsingleton.elim _ _
    rw [hz, spectrum.spectralRadius_zero]
    exact zero_lt_one
  | inr hn =>
    apply spectrum.spectralRadius_lt_of_forall_lt_of_nonempty
      (spectrum.nonempty (cayleyTransform A p))
    intro μ hμ
    rw [spectrum_cayleyTransform A p hp.ne' (hA.isUnit_sub_pos_smul_one p hp)] at hμ
    obtain ⟨z, hz, rfl⟩ := hμ
    exact_mod_cast norm_cayley_lt_one (hA z hz) p hp

end NLAlib
