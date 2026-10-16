import NLAlib.Matrix.Functions.SteinPartialSums
import NLAlib.Matrix.Spectral.MatrixPowerReal
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import NLAlib.Matrix.Basic.QuadForm
import NLAlib.Matrix.Spectral.EigenvectorPairing

/-!
# Convergent Stein Gramians

Finite-dimensional spectral-radius power bounds prove convergence of the
actual Gramian series. The finite identities then give its equation,
uniqueness, exact tails, and positive semidefiniteness.
-/

noncomputable section
open Filter
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology
namespace NLAlib

variable {K n : Type*} [RCLike K] [Fintype n] [DecidableEq n]

/-- The actual infinite Stein Gramian series, with total sum convention. -/
def steinGramian (A Q : Matrix n n K) : Matrix n n K :=
  ∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j

/-- A proved geometric power bound gives absolute convergence of the Gramian
series. This helper is instantiated below from the spectral radius itself. -/
theorem summable_stein_of_power_bound (A Q : Matrix n n K) (C r : ℝ)
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hpow : ∀ j : ℕ, specNorm (A ^ j) ≤ C * r ^ j) :
    Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j) := by
  have hr2 : r ^ 2 < 1 := by nlinarith
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (sq_nonneg r) hr2).mul_left (C ^ 2 * specNorm Q))
  intro j
  rw [← specNorm_eq_norm, ← Matrix.conjTranspose_pow]
  calc
    _ ≤ specNorm (A ^ j * Q) * specNorm (A ^ j)ᴴ := specNorm_mul_le _ _
    _ ≤ (specNorm (A ^ j) * specNorm Q) * specNorm (A ^ j) := by
      rw [specNorm_conjTranspose]
      exact mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
    _ ≤ (C * r ^ j * specNorm Q) * (C * r ^ j) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hpow j) (specNorm_nonneg _)) (hpow j)
        (specNorm_nonneg _) (mul_nonneg (mul_nonneg hC (pow_nonneg hr j)) (specNorm_nonneg _))
    _ = _ := by rw [← pow_mul, mul_comm 2 j, pow_mul]; ring

/-- A convergent Stein series solves the actual equation. -/
theorem steinGramian_sub_mul_mul_conjTranspose (A Q : Matrix n n K)
    (hs : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j)) :
    steinGramian A Q - A * steinGramian A Q * Aᴴ = Q := by
  have hlim : Tendsto (steinPartialSum A Q) atTop (𝓝 (steinGramian A Q)) :=
    hs.hasSum.tendsto_sum_nat
  have hleft : Tendsto (fun N => Q - steinPartialSum A Q N + A * steinPartialSum A Q N * Aᴴ)
      atTop (𝓝 (Q - steinGramian A Q + A * steinGramian A Q * Aᴴ)) :=
    (tendsto_const_nhds.sub hlim).add ((tendsto_const_nhds.mul hlim).mul_const _)
  have hright : Tendsto (fun N => Q - steinPartialSum A Q N + A * steinPartialSum A Q N * Aᴴ)
      atTop (𝓝 0) := by
    simpa only [steinPartialSum_residual] using hs.tendsto_atTop_zero
  have heq := tendsto_nhds_unique hleft hright
  apply eq_of_sub_eq_zero
  have hid : steinGramian A Q - A * steinGramian A Q * Aᴴ - Q =
      -(Q - steinGramian A Q + A * steinGramian A Q * Aᴴ) := by abel
  rw [hid, heq, neg_zero]

/-- The exact infinite Gramian tail is the propagated full Gramian. -/
theorem steinGramian_sub_partialSum (A Q : Matrix n n K)
    (hs : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j)) (N : ℕ) :
    steinGramian A Q - steinPartialSum A Q N = A ^ N * steinGramian A Q * (Aᴴ) ^ N :=
  sub_steinPartialSum_eq A Q _ (steinGramian_sub_mul_mul_conjTranspose A Q hs) N

/-- Decaying matrix powers make the Stein solution unique. -/
theorem eq_steinGramian_of_solution (A Q X : Matrix n n K)
    (hs : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j))
    (hp : Tendsto (fun j : ℕ => A ^ j) atTop (𝓝 0))
    (hX : X - A * X * Aᴴ = Q) : X = steinGramian A Q := by
  have hlim : Tendsto (steinPartialSum A Q) atTop (𝓝 (steinGramian A Q)) :=
    hs.hasSum.tendsto_sum_nat
  have hstar : Tendsto (fun j : ℕ => (Aᴴ) ^ j) atTop (𝓝 0) := by
    have hc : Continuous (fun M : Matrix n n K => Mᴴ) := by fun_prop
    simpa only [Function.comp_def, Matrix.conjTranspose_pow, Matrix.conjTranspose_zero] using
      hc.continuousAt.tendsto.comp hp
  have hzero := (hp.mul_const X).mul hstar
  simp only [Matrix.zero_mul, Matrix.mul_zero] at hzero
  have hid : (fun N => A ^ N * X * (Aᴴ) ^ N) = fun N => X - steinPartialSum A Q N := by
    funext N
    exact (sub_steinPartialSum_eq A Q X hX N).symm
  rw [hid] at hzero
  exact sub_eq_zero.mp (tendsto_nhds_unique (tendsto_const_nhds.sub hlim) hzero)

/-- Convergent Stein Gramians are positive semidefinite for PSD forcing. -/
theorem posSemidef_steinGramian (A Q : Matrix n n K) (hQ : Q.PosSemidef)
    (hs : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j)) : (steinGramian A Q).PosSemidef := by
  have hlim : Tendsto (steinPartialSum A Q) atTop (𝓝 (steinGramian A Q)) :=
    hs.hasSum.tendsto_sum_nat
  have hc : Continuous (fun M : Matrix n n K => Mᴴ) := by fun_prop
  have ht := hc.continuousAt.tendsto.comp hlim
  have hherm : (fun N => (steinPartialSum A Q N)ᴴ) = steinPartialSum A Q :=
    funext fun N => (posSemidef_steinPartialSum A Q hQ N).isHermitian.eq
  simp only [Function.comp_def] at ht
  rw [hherm] at ht
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (tendsto_nhds_unique ht hlim)
  intro x
  have hcont : Continuous (fun M : Matrix n n K => star x ⬝ᵥ (M *ᵥ x)) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (hcont.continuousAt.tendsto.comp hlim)
    (Eventually.of_forall fun N => (posSemidef_steinPartialSum A Q hQ N).dotProduct_mulVec_nonneg x)

/-- The actual complex Gramian series converges for spectral radius below one;
the matrix itself need not have norm below one. Source: user derivations,
Stein Gramians and finite-dimensional geometric power bounds.
atlas: stein-gramian-smith-doubling (partial) -/
theorem summable_stein_of_spectralRadius_lt_one (A Q : Matrix n n ℂ)
    (hA : spectralRadius ℂ A < 1) : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j) := by
  have hρ : (spectralRadius ℂ A).toReal < 1 :=
    (ENNReal.toReal_lt_toReal (matrix_spectralRadius_ne_top A) ENNReal.one_ne_top).mpr hA
  let r := ((spectralRadius ℂ A).toReal + 1) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  obtain ⟨N, hN⟩ := exists_prefix_norm_matrix_pow_le_growth A hr (by dsimp [r]; linarith)
  exact summable_stein_of_power_bound A Q _ r
    (zero_le_one.trans (one_le_matrixPowerBoundConstant A hr N)) hr.le hr1 hN

/-- The same actual Gramian series converges for a real matrix using its
complexified spectral radius. -/
theorem summable_real_stein_of_complex_spectralRadius_lt_one (A Q : Matrix n n ℝ)
    (hA : spectralRadius ℂ (A.map Complex.ofReal) < 1) :
    Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j) := by
  let AC := A.map Complex.ofReal
  have hρ : (spectralRadius ℂ AC).toReal < 1 :=
    (ENNReal.toReal_lt_toReal (matrix_spectralRadius_ne_top AC) ENNReal.one_ne_top).mpr hA
  let ε := (1 - (spectralRadius ℂ AC).toReal) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨N, hN⟩ := exists_prefix_specNorm_real_matrix_pow_le_complex_spectralRadius_add A hε
  have hr : 0 < (spectralRadius ℂ AC).toReal + ε :=
    add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε
  exact summable_stein_of_power_bound A Q _ _
    (zero_le_one.trans (one_le_matrixPowerBoundConstant AC hr N)) hr.le
    (by dsimp [ε]; linarith) hN

/-- Positive definite forcing gives a positive definite Gramian. -/
theorem posDef_steinGramian (A Q : Matrix n n K) (hQ : Q.PosDef)
    (hs : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j)) : (steinGramian A Q).PosDef := by
  have hG := posSemidef_steinGramian A Q hQ.posSemidef hs
  have heq := steinGramian_sub_mul_mul_conjTranspose A Q hs
  rw [eq_add_of_sub_eq heq]
  exact hQ.add_posSemidef (hG.mul_mul_conjTranspose_same A)

/-- A positive definite strict Stein certificate forces every complex
eigenvalue into the unit disk, without normality. -/
theorem norm_lt_one_of_posDef_stein (A X : Matrix n n ℂ) (hX : X.PosDef)
    (hR : (X - A * X * Aᴴ).PosDef) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) : ‖μ‖ < 1 := by
  obtain ⟨y, hy, hyA⟩ := exists_vecMul_eq_smul_of_mem_spectrum hμ
  have hx : star y ≠ 0 := by simpa only [star_ne_zero] using hy
  have hAx : Aᴴ *ᵥ star y = star μ • star y := by
    rw [← Matrix.star_vecMul, hyA, star_smul]
  have hquad : quadForm (A * X * Aᴴ) (star y) =
      (‖μ‖ ^ 2 : ℂ) * quadForm X (star y) := by
    have hc := quadForm_conjTranspose_mul_mul X Aᴴ (star y)
    rw [Matrix.conjTranspose_conjTranspose, hAx, quadForm_smul] at hc
    have hstar : star (star μ) * star μ = (‖μ‖ : ℂ) ^ 2 := by
      rw [star_star]
      exact RCLike.mul_conj μ
    simpa only [hstar] using hc
  have hXp : 0 < (quadForm X (star y)).re := (RCLike.pos_iff.mp (hX.quadForm_pos hx)).1
  have hRp := (RCLike.pos_iff.mp (hR.quadForm_pos hx)).1
  change 0 < (quadForm (X - A * X * Aᴴ) (star y)).re at hRp
  have hreal : (quadForm (X - A * X * Aᴴ) (star y)).re =
      (1 - ‖μ‖ ^ 2) * (quadForm X (star y)).re := by
    rw [quadForm_def, Matrix.sub_mulVec, dotProduct_sub]
    change (quadForm X (star y) - quadForm (A * X * Aᴴ) (star y)).re = _
    rw [hquad]
    simp [Complex.mul_re, ← Complex.ofReal_pow, sub_mul]
  rw [hreal] at hRp
  have hcoef : 0 < 1 - ‖μ‖ ^ 2 := (mul_pos_iff_of_pos_right hXp).mp hRp
  have hnorm : 0 ≤ ‖μ‖ := norm_nonneg μ
  nlinarith

/-- Discrete stability is equivalent to a positive definite strict Stein
certificate. Source: user derivations, Stein stability equivalence.
atlas: stein-gramian-smith-doubling (partial) -/
theorem spectralRadius_lt_one_iff_exists_posDef_stein (A : Matrix n n ℂ) :
    spectralRadius ℂ A < 1 ↔ ∃ X : Matrix n n ℂ, X.PosDef ∧ (X - A * X * Aᴴ).PosDef := by
  constructor
  · intro hA
    have hs := summable_stein_of_spectralRadius_lt_one A 1 hA
    refine ⟨steinGramian A 1, posDef_steinGramian A 1 Matrix.PosDef.one hs, ?_⟩
    rw [steinGramian_sub_mul_mul_conjTranspose A 1 hs]
    exact Matrix.PosDef.one
  · rintro ⟨X, hX, hR⟩
    cases isEmpty_or_nonempty n with
    | inl hn =>
      have hz : A = 0 := Subsingleton.elim _ _
      rw [hz, spectrum.spectralRadius_zero]
      exact zero_lt_one
    | inr hn =>
      apply spectrum.spectralRadius_lt_of_forall_lt_of_nonempty (spectrum.nonempty A)
      intro μ hμ
      exact_mod_cast norm_lt_one_of_posDef_stein A X hX hR hμ

end NLAlib
