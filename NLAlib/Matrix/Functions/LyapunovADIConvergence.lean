import NLAlib.Matrix.Functions.LyapunovADIFactors

/-! # Fixed positive-shift convergence of the actual low-rank ADI process -/
noncomputable section
open Filter
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {n s : Type*} [Fintype n] [Fintype s] [DecidableEq n]

/-- Positive shifts of a Hurwitz matrix make every actual ADI solve admissible. -/
theorem IsHurwitz.lyapunovADI_admissible {A : Matrix n n ℂ} (hA : IsHurwitz A)
    (p : ℕ → ℝ) (hp : ∀ j, 0 < p j) (j : ℕ) :
    IsUnit (A - (p j : ℂ) • 1).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (hA.isUnit_sub_pos_smul_one (p j) (hp j))

/-- The spectral error estimate is obtained from the exact matrix error. -/
theorem specNorm_sub_lyapunovADI_le (A X : Matrix n n ℂ) (B : Matrix n s ℂ)
    (p : ℕ → ℝ) (hP : ∀ j, IsUnit (A - (p j : ℂ) • 1).det)
    (hX : A * X + X * Aᴴ + B * Bᴴ = 0) (j : ℕ) :
    specNorm (X - (lyapunovADI A B p j).2) ≤
      specNorm (lyapunovADIPropagator A p j) ^ 2 * specNorm X := by
  rw [sub_lyapunovADI_snd A X B p hP hX]
  calc
    _ ≤ specNorm (lyapunovADIPropagator A p j * X) * specNorm (lyapunovADIPropagator A p j)ᴴ := specNorm_mul_le _ _
    _ ≤ (specNorm (lyapunovADIPropagator A p j) * specNorm X) * specNorm (lyapunovADIPropagator A p j) := by
      rw [specNorm_conjTranspose]
      exact mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
    _ = _ := by ring

/-- The Frobenius error obeys the same spectral propagator coefficient. -/
theorem frobNorm_sub_lyapunovADI_le (A X : Matrix n n ℂ) (B : Matrix n s ℂ)
    (p : ℕ → ℝ) (hP : ∀ j, IsUnit (A - (p j : ℂ) • 1).det)
    (hX : A * X + X * Aᴴ + B * Bᴴ = 0) (j : ℕ) :
    frobNorm (X - (lyapunovADI A B p j).2) ≤
      specNorm (lyapunovADIPropagator A p j) ^ 2 * frobNorm X := by
  rw [sub_lyapunovADI_snd A X B p hP hX]
  calc
    _ ≤ frobNorm (lyapunovADIPropagator A p j * X) * specNorm (lyapunovADIPropagator A p j)ᴴ := frobNorm_mul_le_frobNorm_mul_specNorm _ _
    _ ≤ (specNorm (lyapunovADIPropagator A p j) * frobNorm X) * specNorm (lyapunovADIPropagator A p j) := by
      rw [specNorm_conjTranspose]
      exact mul_le_mul_of_nonneg_right (frobNorm_mul_le_specNorm_mul_frobNorm _ _) (specNorm_nonneg _)
    _ = _ := by ring

/-- A fixed shift gives the actual powers of its Cayley matrix. -/
theorem lyapunovADIPropagator_const (A : Matrix n n ℂ) (p : ℝ) (j : ℕ) :
    lyapunovADIPropagator A (fun _ => p) j = cayleyTransform A p ^ j := by
  induction j with
  | zero => rfl
  | succ j hj => rw [lyapunovADIPropagator, hj, pow_succ']

/-- For every fixed positive shift, the actual low-rank ADI iterates converge
to the actual improper Gramian for every Hurwitz matrix, with no normality
or small-matrix-norm hypothesis. Arbitrary varying shifts are not asserted
to converge. Source: user derivations, low-rank Lyapunov ADI.
atlas: lyapunov-adi-residual-factor (partial) -/
theorem tendsto_lyapunovADI_snd_const (A : Matrix n n ℂ) (B : Matrix n s ℂ)
    (hA : IsHurwitz A) (p : ℝ) (hp : 0 < p) :
    Tendsto (fun j => (lyapunovADI A B (fun _ => p) j).2) atTop
      (𝓝 (lyapunovGramian A (B * Bᴴ))) := by
  let X := lyapunovGramian A (B * Bᴴ)
  have hEq : A * X + X * Aᴴ + B * Bᴴ = 0 := by
    change A * lyapunovGramian A (B * Bᴴ) + lyapunovGramian A (B * Bᴴ) * Aᴴ + B * Bᴴ = 0
    rw [lyapunovGramian_eq_of_solution A _ _ hA (lyapunovCayleySolution_equation A _ hA)]
    exact lyapunovCayleySolution_equation A _ hA
  have ht := tendsto_matrix_pow_zero_of_spectralRadius_lt_one (hA.spectralRadius_cayleyTransform_lt_one p hp)
  have hstar : Tendsto (fun j : ℕ => (cayleyTransform A p ^ j)ᴴ) atTop (𝓝 0) := by
    have hc : Continuous (fun M : Matrix n n ℂ => Mᴴ) := by fun_prop
    simpa only [Function.comp_def, Matrix.conjTranspose_zero] using hc.continuousAt.tendsto.comp ht
  have he := (ht.mul_const X).mul hstar
  simp only [Matrix.zero_mul, Matrix.mul_zero] at he
  have herror : (fun j => cayleyTransform A p ^ j * X * (cayleyTransform A p ^ j)ᴴ) =
      fun j => X - (lyapunovADI A B (fun _ => p) j).2 := by
    funext j
    rw [sub_lyapunovADI_snd A X B _ (hA.lyapunovADI_admissible _ (fun _ => hp)) hEq,
      lyapunovADIPropagator_const]
  rw [herror] at he
  have hh := (tendsto_const_nhds (x := X) (f := atTop)).sub he
  simpa only [sub_sub_cancel, sub_zero] using hh

end NLAlib
