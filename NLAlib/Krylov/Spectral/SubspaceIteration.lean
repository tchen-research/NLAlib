import NLAlib.Krylov.Spaces.Block
import NLAlib.Matrix.Subspaces.PrincipalAngles
/-!
# Convergence of subspace iteration (symmetric case)

Let `A` have an invariant splitting `ℝⁿ = range U ⊕ range V` with `U : n × s`, `V : n × r`
orthonormal, `UUᵀ + VVᵀ = I`, `A U = U diag(d)`, `A V = V diag(e)` (for symmetric `A`: `U` the
dominant eigenvectors, `V` the others), `|dᵢ| ≥ α > 0` and `|eⱼ| ≤ β`. If `UᵀΩ` is invertible,
then the subspace iterates `S_k = range (A^k Ω)` satisfy

  `tan θ_max(U_s, S_k) ≤ (β/α)^k tan θ_max(U_s, range Ω)`,

with `tan θ_max(U, X) = ‖(I − UUᵀ) X (UᵀX)⁻¹‖₂ = ‖Vᵀ X (UᵀX)⁻¹‖₂` (`tanThetaMax`), which depends
only on `range X` (`tanThetaMax_eq_of_range_eq`), so any basis of `S_k` (in particular any
orthonormal basis the algorithm carries) may be used.

* `tanThetaMax_pow_mul_le`: the bound for the unorthonormalised block `A^k Ω`.
* `tanThetaMax_le_of_range_eq_subspaceIterate`: the same for any bases `Q₀` of `range Ω` and
  `Q_k` of `S_k` (the form of Saad, Thm 5.2).
* `isUnit_transpose_mul_pow_mul`: `Uᵀ A^k Ω` stays invertible.

Proof (K-D's round-8 plan; no Davis–Kahan in the symmetric case): `Uᵀ A^k = D^k Uᵀ`,
`(I − UUᵀ) A^k Ω = V E^k Vᵀ Ω`, so `(I − UUᵀ) A^k Ω (Uᵀ A^k Ω)⁻¹ = V E^k [Vᵀ Ω (UᵀΩ)⁻¹] D^{-k}`
and `‖E^k‖ ≤ β^k`, `‖D^{-k}‖ ≤ α^{-k}`.

Deviation from the atlas statement: the eigen-decomposition enters as matrices `U, V, d, e`
(any invariant splitting, e.g. columns of `hA.eigenvectorUnitary` split by a set of indices)
instead of ordered eigenvalues `λ_s > λ_{s+1} ≥ 0`; `α = |λ_s|`, `β = |λ_{s+1}|` recovers
Saad's rate. The per-vector refinement (rate `(λ_{s+1}/λ_i)^k` for `u_i`) is not stated.

Source: Saad (2011) [`saad11`], Thm 5.2; Golub–Van Loan (2013) [`gvl13`], Thm 8.2.2.
Atlas: `subspace-iteration-convergence`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {n s r : Type*} [Fintype n] [DecidableEq n] [Fintype s] [DecidableEq s] [Fintype r]
  [DecidableEq r]

/-- Ingredients of the convergence proof: with an invariant orthogonal splitting
`UUᵀ + VVᵀ = I`, `AU = U diag(d)`, `AV = V diag(e)`, one has `UᵀV = 0`, `Uᵀ A^k = diag(d)^k Uᵀ`
and `Vᵀ A^k = diag(e)^k Vᵀ`. Source: Saad (2011) [`saad11`], proof of Thm 5.2. Helper for
`subspace-iteration-convergence`. -/
theorem transpose_mul_pow_eq_of_invariant {A : Matrix n n ℝ} {U : Matrix n s ℝ}
    {V : Matrix n r ℝ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hUV : U * Uᵀ + V * Vᵀ = 1) {d : s → ℝ} {e : r → ℝ} (hAU : A * U = U * diagonal d)
    (hAV : A * V = V * diagonal e) (k : ℕ) :
    Uᵀ * A ^ k = diagonal d ^ k * Uᵀ ∧ Vᵀ * A ^ k = diagonal e ^ k * Vᵀ := by
  have hU' : Uᵀ * U = 1 := hU
  have hV' : Vᵀ * V = 1 := hV
  -- `UᵀV = 0`
  have hUtV : Uᵀ * V = 0 := by
    have h1 : Uᵀ * (U * Uᵀ + V * Vᵀ) = Uᵀ := by rw [hUV, Matrix.mul_one]
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hU', Matrix.one_mul, add_eq_left] at h1
    have h2 := congrArg (· * V) h1
    simpa [Matrix.mul_assoc, hV'] using h2
  have hVtU : Vᵀ * U = 0 := by
    have := congrArg Matrix.transpose hUtV
    simpa [Matrix.transpose_mul] using this
  -- `A^k U = U D^k`, `A^k V = V E^k`
  have hpU : ∀ k : ℕ, A ^ k * U = U * diagonal d ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Matrix.mul_assoc, hAU, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
        ← pow_succ]
  have hpV : ∀ k : ℕ, A ^ k * V = V * diagonal e ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Matrix.mul_assoc, hAV, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
        ← pow_succ]
  have hsplit : A ^ k = U * diagonal d ^ k * Uᵀ + V * diagonal e ^ k * Vᵀ := by
    conv_lhs => rw [← Matrix.mul_one (A ^ k), ← hUV]
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hpU, hpV]
  constructor
  · rw [hsplit, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hU', hUtV]
    simp
  · rw [hsplit, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hV', hVtU]
    simp

/-- `Uᵀ A^k Ω = diag(d)^k Uᵀ Ω` stays invertible when `UᵀΩ` is and every `dᵢ ≠ 0`. Source:
Saad (2011) [`saad11`], proof of Thm 5.2. Helper for `subspace-iteration-convergence`. -/
theorem isUnit_transpose_mul_pow_mul {A : Matrix n n ℝ} {U : Matrix n s ℝ}
    {V : Matrix n r ℝ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hUV : U * Uᵀ + V * Vᵀ = 1) {d : s → ℝ} {e : r → ℝ} (hAU : A * U = U * diagonal d)
    (hAV : A * V = V * diagonal e) (hd : ∀ i, d i ≠ 0) {Ω : Matrix n s ℝ}
    (hΩ : IsUnit (Uᵀ * Ω)) (k : ℕ) : IsUnit (Uᵀ * (A ^ k * Ω)) := by
  rw [← Matrix.mul_assoc, (transpose_mul_pow_eq_of_invariant hU hV hUV hAU hAV k).1,
    Matrix.mul_assoc, Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, diagonal_pow,
    Matrix.det_diagonal]
  refine IsUnit.mul (isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_))
    ((Matrix.isUnit_iff_isUnit_det _).1 hΩ)
  exact pow_ne_zero _ (hd i)

/-- **Convergence of subspace iteration (symmetric case).** With an invariant orthogonal
splitting `UUᵀ + VVᵀ = I`, `AU = U diag(d)`, `AV = V diag(e)`, `|dᵢ| ≥ α > 0`, `|eⱼ| ≤ β` and
`UᵀΩ` invertible:
`tan θ_max(range U, range (A^k Ω)) ≤ (β/α)^k tan θ_max(range U, range Ω)`.
Source: Saad (2011) [`saad11`], Thm 5.2 (symmetric case); Golub–Van Loan (2013) [`gvl13`],
Thm 8.2.2. Deviation: invariant splitting `(U, V, d, e)` with bounds `α, β` instead of ordered
eigenvalues (`α = |λ_s|`, `β = |λ_{s+1}|`); the iterate is the block `A^k Ω` (any basis of `S_k`:
`tanThetaMax_le_of_range_eq_subspaceIterate`).
atlas: subspace-iteration-convergence -/
theorem tanThetaMax_pow_mul_le {A : Matrix n n ℝ} {U : Matrix n s ℝ} {V : Matrix n r ℝ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (hUV : U * Uᵀ + V * Vᵀ = 1)
    {d : s → ℝ} {e : r → ℝ} (hAU : A * U = U * diagonal d) (hAV : A * V = V * diagonal e)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hd : ∀ i, α ≤ |d i|) (he : ∀ j, |e j| ≤ β)
    {Ω : Matrix n s ℝ} (hΩ : IsUnit (Uᵀ * Ω)) (k : ℕ) :
    tanThetaMax U (A ^ k * Ω) ≤ (β / α) ^ k * tanThetaMax U Ω := by
  obtain ⟨hUk, hVk⟩ := transpose_mul_pow_eq_of_invariant hU hV hUV hAU hAV k
  have hd0 : ∀ i, d i ≠ 0 := fun i h => by
    have := hd i; rw [h, abs_zero] at this; linarith
  set Dinv : Matrix s s ℝ := diagonal fun i => (d i ^ k)⁻¹ with hDinv
  set Y : Matrix r s ℝ := Vᵀ * Ω * (Uᵀ * Ω)⁻¹ with hY
  have hΩ' : (Uᵀ * Ω)⁻¹ * (Uᵀ * Ω) = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hΩ)
  -- `(Uᵀ A^k Ω)⁻¹ = (UᵀΩ)⁻¹ D^{-k}`
  have hUkΩ : Uᵀ * (A ^ k * Ω) = diagonal d ^ k * (Uᵀ * Ω) := by
    rw [← Matrix.mul_assoc, hUk, Matrix.mul_assoc]
  have hVkΩ : Vᵀ * (A ^ k * Ω) = diagonal e ^ k * (Vᵀ * Ω) := by
    rw [← Matrix.mul_assoc, hVk, Matrix.mul_assoc]
  have h1 : Dinv * diagonal d ^ k = 1 := by
    rw [hDinv, diagonal_pow, diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp [inv_mul_cancel₀ (pow_ne_zero k (hd0 i))]
  have hinv : (Uᵀ * (A ^ k * Ω))⁻¹ = (Uᵀ * Ω)⁻¹ * Dinv := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hUkΩ, Matrix.mul_assoc, ← Matrix.mul_assoc Dinv, h1, Matrix.one_mul, hΩ']
  -- the complement forms
  have h0 : tanThetaMax U Ω = specNorm Y :=
    tanThetaMax_eq_specNorm_transpose_mul_mul U hV hUV Ω
  have hk : tanThetaMax U (A ^ k * Ω) = specNorm (diagonal e ^ k * Y * Dinv) := by
    rw [tanThetaMax_eq_specNorm_transpose_mul_mul U hV hUV, hinv, hVkΩ, hY]
    simp only [Matrix.mul_assoc]
  -- norm bounds
  have hE : specNorm (diagonal e ^ k) ≤ β ^ k := by
    rw [diagonal_pow]
    refine specNorm_diagonal_le (pow_nonneg hβ k) fun j => ?_
    simp only [Pi.pow_apply, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (he j) k
  have hD : specNorm Dinv ≤ (α⁻¹) ^ k := by
    refine specNorm_diagonal_le (pow_nonneg (inv_nonneg.2 hα.le) k) fun i => ?_
    rw [abs_inv, abs_pow, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 (abs_nonneg _)) (inv_anti₀ hα (hd i)) k
  rw [hk, h0]
  calc specNorm (diagonal e ^ k * Y * Dinv)
      ≤ specNorm (diagonal e ^ k * Y) * specNorm Dinv := specNorm_mul_le _ _
    _ ≤ (specNorm (diagonal e ^ k) * specNorm Y) * (α⁻¹) ^ k :=
        mul_le_mul (specNorm_mul_le _ _) hD (specNorm_nonneg _)
          (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))
    _ ≤ (β ^ k * specNorm Y) * (α⁻¹) ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE (specNorm_nonneg _))
          (pow_nonneg (inv_nonneg.2 hα.le) k)
    _ = (β / α) ^ k * specNorm Y := by rw [div_eq_mul_inv, mul_pow]; ring

/-- **Convergence of subspace iteration, basis form.** Under the hypotheses of
`tanThetaMax_pow_mul_le`, for any `Q₀` with `range Q₀ = range Ω` and any `Q_k` with
`range Q_k = S_k = subspaceIterate A Ω k` (for instance the orthonormal bases the algorithm
carries), `tan θ_max(range U, range Q_k) ≤ (β/α)^k tan θ_max(range U, range Q₀)`.
Source: Saad (2011) [`saad11`], Thm 5.2; Golub–Van Loan (2013) [`gvl13`], Thm 8.2.2.
atlas: subspace-iteration-convergence -/
theorem tanThetaMax_le_of_range_eq_subspaceIterate {A : Matrix n n ℝ} {U : Matrix n s ℝ}
    {V : Matrix n r ℝ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hUV : U * Uᵀ + V * Vᵀ = 1) {d : s → ℝ} {e : r → ℝ} (hAU : A * U = U * diagonal d)
    (hAV : A * V = V * diagonal e) {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hd : ∀ i, α ≤ |d i|) (he : ∀ j, |e j| ≤ β) {Ω : Matrix n s ℝ} (hΩ : IsUnit (Uᵀ * Ω))
    {k : ℕ} {Q₀ Qk : Matrix n s ℝ}
    (hQ₀ : LinearMap.range Q₀.mulVecLin = LinearMap.range Ω.mulVecLin)
    (hQk : LinearMap.range Qk.mulVecLin = subspaceIterate A Ω k) :
    tanThetaMax U Qk ≤ (β / α) ^ k * tanThetaMax U Q₀ := by
  have hd0 : ∀ i, d i ≠ 0 := fun i h => by
    have := hd i; rw [h, abs_zero] at this; linarith
  rw [← tanThetaMax_eq_of_range_eq U hQk.symm
      (isUnit_transpose_mul_pow_mul hU hV hUV hAU hAV hd0 hΩ k),
    ← tanThetaMax_eq_of_range_eq U hQ₀.symm hΩ]
  exact tanThetaMax_pow_mul_le hU hV hUV hAU hAV hα hβ hd he hΩ k

end NLAlib
