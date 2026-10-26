import NLAlib.Krylov.Solvers.StationarySplitting
import NLAlib.Matrix.Nonnegative.MMatrixSpectral

/-!
# Regular splittings and inverse positivity

For a regular splitting `A = M - N`, with `M⁻¹` and `N` entrywise nonnegative,
inverse positivity of `A` is equivalent to spectral-radius convergence of `M⁻¹N`.
No Z-matrix assumption on `A` is required. The forward proof pairs a positive vector
`A⁻¹ 1` with a nonnegative left Perron vector; the converse factors `A = M (I - M⁻¹N)`.

Source: Meyer (2023), Theorem 4.11.9 and (4.11.24), pp. 623–625. The regular-splitting
hypotheses include `N ≥ 0`, which the printed proof uses.
-/

noncomputable section
open Matrix Finset Filter
open scoped Matrix Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem row_sum_pos_of_nonneg_isUnit {B : Matrix n n ℝ}
    (hB : IsUnit B) (hpos : ∀ i j, 0 ≤ B i j) (i : n) : 0 < ∑ j, B i j := by
  have hs : 0 ≤ ∑ j, B i j := Finset.sum_nonneg fun j _ => hpos i j
  apply lt_of_le_of_ne hs
  intro hz
  have hrow : ∀ j, B i j = 0 := fun j =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hpos i k)).mp hz.symm j (mem_univ j)
  have hid := congrArg (fun C : Matrix n n ℝ => C i i)
    (Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB))
  simp [Matrix.mul_apply, hrow] at hid

omit [DecidableEq n] in
private theorem dotProduct_pos_of_nonneg_sum_one {q x : n → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i = 1) (hx : ∀ i, 0 < x i) : 0 < q ⬝ᵥ x := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < q j := by
    by_contra! h
    have hle := Finset.sum_nonpos (fun j (_ : j ∈ Finset.univ) => h j)
    rw [hs] at hle
    norm_num at hle
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hq i) (hx i).le)
    ⟨j, mem_univ j, mul_pos hj (hx j)⟩

/-- An inverse-positive regular splitting has iteration spectral radius strictly below one.
The spectral radius is taken after complexification, so nonreal eigenvalues are included.
atlas: regular-splitting-inverse-positivity (partial) -/
theorem complex_spectralRadius_inv_mul_lt_one_of_inverse_nonneg [Nonempty n]
    {M N : Matrix n n ℝ} (hM : IsUnit M) (hMinv : ∀ i j, 0 ≤ M⁻¹ i j)
    (hN : ∀ i j, 0 ≤ N i j) (hA : IsUnit (M - N))
    (hAinv : ∀ i j, 0 ≤ (M - N)⁻¹ i j) :
    spectralRadius ℂ ((M⁻¹ * N).map Complex.ofReal) < 1 := by
  let H := M⁻¹ * N
  have hH : ∀ i j, 0 ≤ H i j := fun i j =>
    Finset.sum_nonneg fun k _ => mul_nonneg (hMinv i k) (hN k j)
  let x : n → ℝ := (M - N)⁻¹ *ᵥ (fun _ => 1)
  let d : n → ℝ := M⁻¹ *ᵥ (fun _ => 1)
  have hx : ∀ i, 0 < x i := fun i => by
    simpa [x, Matrix.mulVec, dotProduct] using
      row_sum_pos_of_nonneg_isUnit (Matrix.isUnit_nonsing_inv_iff.mpr hA) hAinv i
  have hd : ∀ i, 0 < d i := fun i => by
    simpa [d, Matrix.mulVec, dotProduct] using
      row_sum_pos_of_nonneg_isUnit (Matrix.isUnit_nonsing_inv_iff.mpr hM) hMinv i
  have hAx : (M - N) *ᵥ x = fun _ => 1 := by
    dsimp only [x]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hA), Matrix.one_mulVec]
  have hfix : H *ᵥ x + d = x := (splitting_fixedPoint_iff hM _ x).mpr hAx
  obtain ⟨_, q, _, hq, _, hqs, _, hqH⟩ := Matrix.exists_nonnegative_perron_pair hH
  have hqx := dotProduct_pos_of_nonneg_sum_one hq hqs hx
  have hqd := dotProduct_pos_of_nonneg_sum_one hq hqs hd
  have heq := congrArg (fun v => q ⬝ᵥ v) hfix
  rw [dotProduct_add, Matrix.dotProduct_mulVec, hqH, smul_dotProduct, smul_eq_mul] at heq
  have hr : (spectralRadius ℂ (H.map Complex.ofReal)).toReal < 1 := by nlinarith
  exact (ENNReal.toReal_lt_toReal (matrix_spectralRadius_ne_top _) ENNReal.one_ne_top).mp hr

/-- A convergent regular splitting is invertible and inverse-positive.
atlas: regular-splitting-inverse-positivity (partial) -/
theorem inverse_nonneg_of_complex_spectralRadius_inv_mul_lt_one [Nonempty n]
    {M N : Matrix n n ℝ} (hM : IsUnit M) (hMinv : ∀ i j, 0 ≤ M⁻¹ i j)
    (hN : ∀ i j, 0 ≤ N i j)
    (hρ : spectralRadius ℂ ((M⁻¹ * N).map Complex.ofReal) < 1) :
    IsUnit (M - N) ∧ ∀ i j, 0 ≤ (M - N)⁻¹ i j := by
  let H := M⁻¹ * N
  have hH : ∀ i j, 0 ≤ H i j := fun i j =>
    Finset.sum_nonneg fun k _ => mul_nonneg (hMinv i k) (hN k j)
  have hZ : (1 - H).IsZMatrix := by
    intro i j hij
    simp only [Matrix.sub_apply, Matrix.one_apply, hij, if_false, zero_sub]
    exact neg_nonpos.mpr (hH i j)
  have hr : (spectralRadius ℂ (H.map Complex.ofReal)).toReal < 1 :=
    (ENNReal.toReal_lt_toReal (matrix_spectralRadius_ne_top _) ENNReal.one_ne_top).mpr hρ
  have hB : (1 - H).IsNonsingularMMatrix :=
    (Matrix.isNonsingularMMatrix_iff_exists_shift_above_spectralRadius hZ).mpr
      ⟨1, H, hH, by simp, hr⟩
  have hfactor : M - N = M * (1 - H) := sub_eq_mul_one_sub_inv_mul hM
  have hunit : IsUnit (M - N) := by rw [hfactor]; exact hM.mul hB.2.1
  have hinv : (M - N)⁻¹ = (1 - H)⁻¹ * M⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [hfactor, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - H),
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hB.2.1),
      Matrix.one_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM)]
  refine ⟨hunit, fun i j => ?_⟩
  rw [hinv]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hB.2.2 i k) (hMinv k j)

/-- The inverse-positive and spectral-radius criteria for a regular splitting are equivalent.
Both regularity assumptions are explicit; no Z-matrix condition on `M - N` is imposed.
atlas: regular-splitting-inverse-positivity (partial) -/
theorem inverse_nonneg_iff_complex_spectralRadius_inv_mul_lt_one [Nonempty n]
    {M N : Matrix n n ℝ} (hM : IsUnit M) (hMinv : ∀ i j, 0 ≤ M⁻¹ i j)
    (hN : ∀ i j, 0 ≤ N i j) :
    (IsUnit (M - N) ∧ ∀ i j, 0 ≤ (M - N)⁻¹ i j) ↔
      spectralRadius ℂ ((M⁻¹ * N).map Complex.ofReal) < 1 :=
  ⟨fun h => complex_spectralRadius_inv_mul_lt_one_of_inverse_nonneg hM hMinv hN h.1 h.2,
    inverse_nonneg_of_complex_spectralRadius_inv_mul_lt_one hM hMinv hN⟩

/-- Every regular splitting of an inverse-positive matrix converges to the actual solution
`(M - N)⁻¹ b`, for every right-hand side and starting vector.
atlas: regular-splitting-inverse-positivity (partial) -/
theorem tendsto_splittingIterate_of_inverse_nonneg [Nonempty n]
    {M N : Matrix n n ℝ} (hM : IsUnit M) (hMinv : ∀ i j, 0 ≤ M⁻¹ i j)
    (hN : ∀ i j, 0 ≤ N i j) (hA : IsUnit (M - N))
    (hAinv : ∀ i j, 0 ≤ (M - N)⁻¹ i j) (b x₀ : n → ℝ) :
    Tendsto (splittingIterate M N b x₀) atTop (𝓝 ((M - N)⁻¹ *ᵥ b)) := by
  have hc := (splittingConverges_iff_complex_spectralRadius_lt_one hM).mpr
    (complex_spectralRadius_inv_mul_lt_one_of_inverse_nonneg hM hMinv hN hA hAinv)
  obtain ⟨xs, _, huniq, hlim⟩ := hc b
  have hsol : (M - N) *ᵥ ((M - N)⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hA), Matrix.one_mulVec]
  rw [huniq _ hsol]
  exact hlim x₀

/-- Nonnegative data produce nonnegative, increasing iterates bounded by the true solution,
when a regular inverse-positive splitting starts from zero.
atlas: regular-splitting-inverse-positivity (partial) -/
theorem splittingIterate_zero_nonneg_mono_le_of_inverse_nonneg
    {M N : Matrix n n ℝ} (hM : IsUnit M) (hMinv : ∀ i j, 0 ≤ M⁻¹ i j)
    (hN : ∀ i j, 0 ≤ N i j) (hA : IsUnit (M - N))
    (hAinv : ∀ i j, 0 ≤ (M - N)⁻¹ i j) {b : n → ℝ} (hb : ∀ i, 0 ≤ b i)
    (k : ℕ) (i : n) :
    0 ≤ splittingIterate M N b 0 k i ∧
      splittingIterate M N b 0 k i ≤ splittingIterate M N b 0 (k + 1) i ∧
      splittingIterate M N b 0 (k + 1) i ≤ ((M - N)⁻¹ *ᵥ b) i := by
  let H := M⁻¹ * N
  let d := M⁻¹ *ᵥ b
  let xs := (M - N)⁻¹ *ᵥ b
  have hH : ∀ i j, 0 ≤ H i j := fun i j =>
    Finset.sum_nonneg fun j' _ => mul_nonneg (hMinv i j') (hN j' j)
  have hd : ∀ i, 0 ≤ d i := fun i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hMinv i j) (hb j)
  have hxs : ∀ i, 0 ≤ xs i := fun i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hAinv i j) (hb j)
  have hmap : ∀ {u v : n → ℝ}, (∀ i, u i ≤ v i) → ∀ i, (H *ᵥ u) i ≤ (H *ᵥ v) i := by
    intro u v huv j
    exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (huv l) (hH j l)
  have hfix : H *ᵥ xs + d = xs := (splitting_fixedPoint_iff hM b xs).mpr (by
    dsimp only [xs]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hA), Matrix.one_mulVec])
  have hnonneg (j : ℕ) : ∀ l, 0 ≤ splittingIterate M N b 0 j l := by
    induction j with
    | zero => simp
    | succ j ih =>
      intro l
      rw [splittingIterate_succ]
      exact add_nonneg (Finset.sum_nonneg fun t _ => mul_nonneg (hH l t) (ih t)) (hd l)
  have hinc (j : ℕ) : ∀ l,
      splittingIterate M N b 0 j l ≤ splittingIterate M N b 0 (j + 1) l := by
    induction j with
    | zero => intro l; simpa using hnonneg 1 l
    | succ j ih =>
      intro l
      calc
        _ = (H *ᵥ splittingIterate M N b 0 j) l + d l := rfl
        _ ≤ (H *ᵥ splittingIterate M N b 0 (j + 1)) l + d l := by
          linarith [hmap ih l]
        _ = _ := rfl
  have hupper (j : ℕ) : ∀ l, splittingIterate M N b 0 j l ≤ xs l := by
    induction j with
    | zero => intro l; simpa using hxs l
    | succ j ih =>
      intro l
      change (H *ᵥ splittingIterate M N b 0 j) l + d l ≤ xs l
      have he : (H *ᵥ xs) l + d l = xs l := congrFun hfix l
      linarith [hmap ih l]
  exact ⟨hnonneg k i, hinc k i, hupper (k + 1) i⟩

/-- Every regular splitting of a nonsingular M-matrix converges.
atlas: regular-splitting-inverse-positivity (partial) -/
theorem splittingConverges_of_isNonsingularMMatrix [Nonempty n]
    {M N : Matrix n n ℝ} (hM : IsUnit M) (hMinv : ∀ i j, 0 ≤ M⁻¹ i j)
    (hN : ∀ i j, 0 ≤ N i j) (hA : (M - N).IsNonsingularMMatrix) :
    SplittingConverges M N :=
  (splittingConverges_iff_complex_spectralRadius_lt_one hM).mpr
    (complex_spectralRadius_inv_mul_lt_one_of_inverse_nonneg hM hMinv hN hA.2.1 hA.2.2)

end NLAlib
