import NLAlib.Matrix.Functions.SteinGeometricBounds

/-! # Convergence of the actual Smith doubling process -/

noncomputable section
open Filter
open scoped Matrix MatrixOrder ComplexOrder Topology
namespace NLAlib
variable {K n : Type*} [RCLike K] [Fintype n] [DecidableEq n]

/-- Every summable actual Stein series is the limit of the actual Smith
iterates, whose prefix lengths are exactly `2^j`.
Source: user derivations, Stein Gramians and Smith doubling.
atlas: stein-gramian-smith-doubling (partial) -/
theorem tendsto_smithDoubling_snd (A Q : Matrix n n K)
    (hs : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j)) :
    Tendsto (fun j => (smithDoubling A Q j).2) atTop (𝓝 (steinGramian A Q)) := by
  have ht : Tendsto (fun j : ℕ => 2 ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))
  simpa only [Function.comp_def, smithDoubling_eq, steinPartialSum, steinGramian] using hs.hasSum.tendsto_sum_nat.comp ht

/-- Smith doubling converges monotonically to the actual complex Stein
Gramian under the spectral-radius hypothesis itself. -/
theorem monotone_tendsto_smithDoubling_of_spectralRadius_lt_one (A Q : Matrix n n ℂ)
    (hA : spectralRadius ℂ A < 1) (hQ : Q.PosSemidef) :
    Monotone (fun j => (smithDoubling A Q j).2) ∧
    Tendsto (fun j => (smithDoubling A Q j).2) atTop (𝓝 (steinGramian A Q)) := by
  refine ⟨?_, tendsto_smithDoubling_snd A Q (summable_stein_of_spectralRadius_lt_one A Q hA)⟩
  intro i j hij
  simp only [smithDoubling_eq]
  exact monotone_steinPartialSum A Q hQ (Nat.pow_le_pow_right (by norm_num) hij)

/-- The same actual Smith process converges for real matrices with stable
complexified spectrum. -/
theorem tendsto_real_smithDoubling_snd (A Q : Matrix n n ℝ)
    (hA : spectralRadius ℂ (A.map Complex.ofReal) < 1) :
    Tendsto (fun j => (smithDoubling A Q j).2) atTop (𝓝 (steinGramian A Q)) :=
  tendsto_smithDoubling_snd A Q (summable_real_stein_of_complex_spectralRadius_lt_one A Q hA)

end NLAlib
