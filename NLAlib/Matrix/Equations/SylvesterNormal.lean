import NLAlib.Matrix.Equations.SylvesterSeparation
import NLAlib.Matrix.Norms.UnitaryInvariance
import NLAlib.Matrix.Spectral.NormalSpectral

/-! # The sharp spectral-distance formula for normal Sylvester operators -/
noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {K m n : Type*} [RCLike K] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
private theorem diagonal_sylvester (a : m → K) (b : n → K) (X : Matrix m n K) :
    Matrix.diagonal a * X - X * Matrix.diagonal b = fun i j => (a i - b j) * X i j := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

open scoped Matrix.Norms.L2Operator in
private theorem diagonal_sylvester_lower (a : m → K) (b : n → K) (c : ℝ) (hc : 0 ≤ c)
    (hmin : ∀ i j, c ≤ ‖a i - b j‖) (X : Matrix m n K) :
    c * frobNorm X ≤ frobNorm (Matrix.diagonal a * X - X * Matrix.diagonal b) := by
  apply le_of_pow_le_pow_left₀ two_ne_zero (frobNorm_nonneg _)
  rw [mul_pow, frobNorm_sq, frobNorm_sq, diagonal_sylvester, frobSq_eq_sum_norm_sq,
    frobSq_eq_sum_norm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc (hmin i j) 2) (sq_nonneg _)

open scoped Matrix.Norms.L2Operator in
/-- For diagonal coefficients, separation is the attained minimum of all
pairwise diagonal distances. -/
theorem isLeast_sylvesterSep_diagonal [Nonempty m] [Nonempty n] (a : m → K) (b : n → K) :
    IsLeast (Set.range (fun ij : m × n => ‖a ij.1 - b ij.2‖))
      (sylvesterSep (Matrix.diagonal a) (Matrix.diagonal b)) := by
  classical
  let f : m × n → ℝ := fun ij => ‖a ij.1 - b ij.2‖
  let S := Finset.univ.image f
  have hS : S.Nonempty := Finset.univ_nonempty.image f
  let c := S.min' hS
  have hcS : c ∈ S := Finset.min'_mem S hS
  obtain ⟨ij, _, hij⟩ := Finset.mem_image.mp hcS
  have hmin (i : m) (j : n) : c ≤ ‖a i - b j‖ :=
    Finset.min'_le S _ (Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩)
  have hc : 0 ≤ c := by rw [← hij]; exact norm_nonneg _
  have hlow : c ≤ sylvesterSep (Matrix.diagonal a) (Matrix.diagonal b) := by
    obtain ⟨X, hX, hR⟩ := exists_frobNorm_one_sylvester_eq_sep (Matrix.diagonal a) (Matrix.diagonal b)
    simpa only [hX, mul_one, hR] using diagonal_sylvester_lower a b c hc hmin X
  let E : Matrix m n K := fun i j => if i = ij.1 then if j = ij.2 then 1 else 0 else 0
  have hE : frobNorm E = 1 := by
    have hsq : frobNorm E ^ 2 = 1 := by
      rw [frobNorm_sq, frobSq_eq_sum_norm_sq]
      simp [E, apply_ite]
    nlinarith [frobNorm_nonneg E]
  have hRE : Matrix.diagonal a * E - E * Matrix.diagonal b = (a ij.1 - b ij.2) • E := by
    rw [diagonal_sylvester]
    ext i j
    by_cases hi : i = ij.1 <;> by_cases hj : j = ij.2 <;>
      simp [E, hi, hj]
  have hupp : sylvesterSep (Matrix.diagonal a) (Matrix.diagonal b) ≤ c := by
    have hh := sylvesterSep_mul_frobNorm_le (Matrix.diagonal a) (Matrix.diagonal b) E
    rw [hE, mul_one, hRE, frobNorm_smul_eq_norm_mul, hE, mul_one] at hh
    exact hh.trans_eq hij
  have heq : sylvesterSep (Matrix.diagonal a) (Matrix.diagonal b) = c := le_antisymm hupp hlow
  refine ⟨⟨ij, hij.trans heq.symm⟩, ?_⟩
  rintro x ⟨⟨i,j⟩, rfl⟩
  rw [heq]
  exact hmin i j

open scoped Matrix.Norms.L2Operator in
private theorem sylvesterSep_unitary_conj_le [Nonempty m] [Nonempty n]
    (A : Matrix m m K) (B : Matrix n n K)
    (U : Matrix.unitaryGroup m K) (V : Matrix.unitaryGroup n K) :
    sylvesterSep ((U : Matrix m m K) * A * (U : Matrix m m K)ᴴ)
      ((V : Matrix n n K) * B * (V : Matrix n n K)ᴴ) ≤ sylvesterSep A B := by
  have hU : (U : Matrix m m K)ᴴ * (U : Matrix m m K) = 1 := Unitary.coe_star_mul_self U
  have hV : (V : Matrix n n K)ᴴ * (V : Matrix n n K) = 1 := Unitary.coe_star_mul_self V
  obtain ⟨Y, hY, hR⟩ := exists_frobNorm_one_sylvester_eq_sep A B
  let X := (U : Matrix m m K) * Y * (V : Matrix n n K)ᴴ
  have hX : frobNorm X = 1 := by
    change frobNorm ((U : Matrix m m K) * Y * ((star V : Matrix.unitaryGroup n K) : Matrix n n K)) = 1
    rw [frobNorm_mul_right_unitary, frobNorm_mul_left_unitary, hY]
  have hEq : ((U : Matrix m m K) * A * (U : Matrix m m K)ᴴ) * X -
      X * ((V : Matrix n n K) * B * (V : Matrix n n K)ᴴ) =
      (U : Matrix m m K) * (A * Y - Y * B) * (V : Matrix n n K)ᴴ := by
    dsimp only [X]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix m m K)ᴴ (U : Matrix m m K) (Y * (V : Matrix n n K)ᴴ), hU,
      Matrix.one_mul, ← Matrix.mul_assoc (V : Matrix n n K)ᴴ (V : Matrix n n K) (B * (V : Matrix n n K)ᴴ),
      hV, Matrix.one_mul]
  have hh := sylvesterSep_mul_frobNorm_le ((U : Matrix m m K) * A * (U : Matrix m m K)ᴴ)
    ((V : Matrix n n K) * B * (V : Matrix n n K)ᴴ) X
  rw [hX, mul_one, hEq] at hh
  change _ ≤ frobNorm ((U : Matrix m m K) * (A * Y - Y * B) * ((star V : Matrix.unitaryGroup n K) : Matrix n n K)) at hh
  rw [frobNorm_mul_right_unitary, frobNorm_mul_left_unitary, hR] at hh
  exact hh

open scoped Matrix.Norms.L2Operator in
/-- Independent unitary changes of the row and column coordinates preserve
Frobenius Sylvester separation exactly. -/
theorem sylvesterSep_unitary_conj [Nonempty m] [Nonempty n]
    (A : Matrix m m K) (B : Matrix n n K)
    (U : Matrix.unitaryGroup m K) (V : Matrix.unitaryGroup n K) :
    sylvesterSep ((U : Matrix m m K) * A * (U : Matrix m m K)ᴴ)
      ((V : Matrix n n K) * B * (V : Matrix n n K)ᴴ) = sylvesterSep A B := by
  have hU : (U : Matrix m m K)ᴴ * (U : Matrix m m K) = 1 := Unitary.coe_star_mul_self U
  have hV : (V : Matrix n n K)ᴴ * (V : Matrix n n K) = 1 := Unitary.coe_star_mul_self V
  apply le_antisymm (sylvesterSep_unitary_conj_le A B U V)
  have h := sylvesterSep_unitary_conj_le ((U : Matrix m m K) * A * (U : Matrix m m K)ᴴ)
    ((V : Matrix n n K) * B * (V : Matrix n n K)ᴴ) (star U) (star V)
  have hbackU : ((star U : Matrix.unitaryGroup m K) : Matrix m m K) *
      ((U : Matrix m m K) * A * (U : Matrix m m K)ᴴ) *
      (((star U : Matrix.unitaryGroup m K) : Matrix m m K))ᴴ = A := by
    change (U : Matrix m m K)ᴴ * ((U : Matrix m m K) * A * (U : Matrix m m K)ᴴ) *
      ((U : Matrix m m K)ᴴ)ᴴ = A
    rw [Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc (U : Matrix m m K)ᴴ ((U : Matrix m m K) * A) (U : Matrix m m K)ᴴ,
      ← Matrix.mul_assoc (U : Matrix m m K)ᴴ (U : Matrix m m K) A,
      hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]
  have hbackV : ((star V : Matrix.unitaryGroup n K) : Matrix n n K) *
      ((V : Matrix n n K) * B * (V : Matrix n n K)ᴴ) *
      (((star V : Matrix.unitaryGroup n K) : Matrix n n K))ᴴ = B := by
    change (V : Matrix n n K)ᴴ * ((V : Matrix n n K) * B * (V : Matrix n n K)ᴴ) *
      ((V : Matrix n n K)ᴴ)ᴴ = B
    rw [Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc (V : Matrix n n K)ᴴ ((V : Matrix n n K) * B) (V : Matrix n n K)ᴴ,
      ← Matrix.mul_assoc (V : Matrix n n K)ᴴ (V : Matrix n n K) B,
      hV, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one]
  rw [hbackU, hbackV] at h
  exact h


open scoped Matrix.Norms.L2Operator in
/-- For arbitrary complex normal coefficients, the sharp Frobenius separation
is exactly the attained distance between their actual spectra. This clause
is not claimed for nonnormal coefficients. Source: user derivations, normal
Sylvester separation.
atlas: sylvester-separation-residual-conditioning -/
theorem isLeast_sylvesterSep_spectral_distances_of_normal [Nonempty m] [Nonempty n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (hA : A * Aᴴ = Aᴴ * A) (hB : B * Bᴴ = Bᴴ * B) :
    IsLeast {c : ℝ | ∃ a ∈ spectrum ℂ A, ∃ b ∈ spectrum ℂ B, ‖a - b‖ = c}
      (sylvesterSep A B) := by
  obtain ⟨U, a, rfl⟩ := exists_unitary_diagonalization_of_normal hA
  obtain ⟨V, b, rfl⟩ := exists_unitary_diagonalization_of_normal hB
  have hspecU : spectrum ℂ ((U : Matrix m m ℂ) * Matrix.diagonal a * (U : Matrix m m ℂ)ᴴ) = Set.range a := by
    simpa only [← Matrix.star_eq_conjTranspose, Unitary.coe_star, spectrum_diagonal] using
      (Unitary.spectrum_star_right_conjugate (R := ℂ) (a := Matrix.diagonal a) (U := U))
  have hspecV : spectrum ℂ ((V : Matrix n n ℂ) * Matrix.diagonal b * (V : Matrix n n ℂ)ᴴ) = Set.range b := by
    simpa only [← Matrix.star_eq_conjTranspose, Unitary.coe_star, spectrum_diagonal] using
      (Unitary.spectrum_star_right_conjugate (R := ℂ) (a := Matrix.diagonal b) (U := V))
  rw [sylvesterSep_unitary_conj, hspecU, hspecV]
  have hset : {c : ℝ | ∃ x ∈ Set.range a, ∃ y ∈ Set.range b, ‖x-y‖ = c} =
      Set.range (fun ij : m × n => ‖a ij.1-b ij.2‖) := by
    ext c
    constructor
    · rintro ⟨x, ⟨i,rfl⟩, y, ⟨j,rfl⟩, rfl⟩
      exact ⟨(i,j), rfl⟩
    · rintro ⟨⟨i,j⟩, rfl⟩
      exact ⟨a i, ⟨i,rfl⟩, b j, ⟨j,rfl⟩, rfl⟩
  rw [hset]
  exact isLeast_sylvesterSep_diagonal a b

end NLAlib
