import NLAlib.Matrix.Functions.LyapunovADIConvergence
import NLAlib.Matrix.Functions.LyapunovReal
import NLAlib.Matrix.Spectral.ComplexificationUnits

/-! # Real positive-shift ADI and its actual Gramian limit -/
noncomputable section
open Filter
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {n s : Type*} [Fintype n] [Fintype s] [DecidableEq n]

/-- Positive shifts also make the actual real solves nonsingular. -/
theorem isUnit_real_sub_pos_of_hurwitz_complexification (A : Matrix n n ℝ)
    (hA : IsHurwitz (realMatrixComplexification A : Matrix n n ℂ))
    (p : ℝ) (hp : 0 < p) : IsUnit (A - p • 1) := by
  apply (isUnit_realMatrixComplexification_iff _).mp
  have h := hA.isUnit_sub_pos_smul_one p hp
  have he : (realMatrixComplexification (A - p • 1) : Matrix n n ℂ) =
      realMatrixComplexification A - (p : ℂ) • 1 := by
    simp only [map_sub, map_smul, map_one]
    congr 1
  rw [he]
  exact h

/-- The actual real Cayley matrix extends to the actual complex Cayley matrix. -/
theorem realMatrixComplexification_cayleyTransform (A : Matrix n n ℝ) (p : ℝ)
    (hP : IsUnit (A - p • 1)) :
    (realMatrixComplexification (cayleyTransform A p) : Matrix n n ℂ) =
      cayleyTransform (realMatrixComplexification A) p := by
  unfold cayleyTransform
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [map_mul, realMatrixComplexification_inv hP]
  simp only [map_add, map_sub, map_smul, map_one]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]

/-- Real Cayley powers genuinely decay for every positive shift of a real
matrix with Hurwitz complexified spectrum. -/
theorem tendsto_real_cayleyTransform_pow_zero (A : Matrix n n ℝ)
    (hA : IsHurwitz (realMatrixComplexification A : Matrix n n ℂ))
    (p : ℝ) (hp : 0 < p) :
    Tendsto (fun j : ℕ => cayleyTransform A p ^ j) atTop (𝓝 0) := by
  apply (tendsto_real_matrix_pow_zero_iff_complex_spectralRadius_lt_one _).mpr
  change spectralRadius ℂ (realMatrixComplexification (cayleyTransform A p) : Matrix n n ℂ) < 1
  rw [realMatrixComplexification_cayleyTransform A p (isUnit_real_sub_pos_of_hurwitz_complexification A hA p hp)]
  exact hA.spectralRadius_cayleyTransform_lt_one p hp

/-- For real data the actual ADI process converges to the actual real improper
Gramian for every fixed positive shift. Source: user derivations, low-rank ADI.
atlas: lyapunov-adi-residual-factor -/
theorem tendsto_real_lyapunovADI_snd_const (A : Matrix n n ℝ) (B : Matrix n s ℝ)
    (hA : IsHurwitz (realMatrixComplexification A : Matrix n n ℂ)) (p : ℝ) (hp : 0 < p) :
    Tendsto (fun j => (lyapunovADI A B (fun _ => p) j).2) atTop
      (𝓝 (realLyapunovGramian A (B * Bᴴ))) := by
  let X := realLyapunovGramian A (B * Bᴴ)
  have hEq : A * X + X * Aᴴ + B * Bᴴ = 0 := (realLyapunovGramian_equation_unique A _ hA).1
  have hP : ∀ j : ℕ, IsUnit (A - ((fun _ : ℕ => p) j) • 1).det := fun _ =>
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_real_sub_pos_of_hurwitz_complexification A hA p hp)
  have ht := tendsto_real_cayleyTransform_pow_zero A hA p hp
  have hstar : Tendsto (fun j : ℕ => (cayleyTransform A p ^ j)ᴴ) atTop (𝓝 0) := by
    have hc : Continuous (fun M : Matrix n n ℝ => Mᴴ) := by fun_prop
    simpa only [Function.comp_def, Matrix.conjTranspose_zero] using hc.continuousAt.tendsto.comp ht
  have he := (ht.mul_const X).mul hstar
  simp only [Matrix.zero_mul, Matrix.mul_zero] at he
  have herror : (fun j => cayleyTransform A p ^ j * X * (cayleyTransform A p ^ j)ᴴ) =
      fun j => X - (lyapunovADI A B (fun _ => p) j).2 := by
    funext j
    rw [sub_lyapunovADI_snd A X B _ hP hEq]
    have hconst (j : ℕ) : lyapunovADIPropagator A (fun _ => p) j = cayleyTransform A p ^ j := by
      induction j with
      | zero => rfl
      | succ j hj => rw [lyapunovADIPropagator, hj, pow_succ']
    rw [hconst]
  rw [herror] at he
  have hh := (tendsto_const_nhds (x := X) (f := atTop)).sub he
  simpa only [sub_sub_cancel, sub_zero] using hh

end NLAlib
