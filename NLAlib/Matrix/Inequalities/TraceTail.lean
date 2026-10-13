import NLAlib.Matrix.Spectral.CourantFischer
import NLAlib.Matrix.Spectral.TraceEigenvalues

/-!
# Trace-square lower bounds from an upper spectral tail

Loewner eigenvalue monotonicity and finite Cauchy--Schwarz give the scalar
energy lower bound used by randomly pivoted Cholesky. Chen–Epperly–Tropp–Webber 2023
(RPCholesky), proof of Theorem 3.1.
-/

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder
namespace NLAlib

/-- A nonnegative finite sequence has squared energy at least the squared excess
above its complementary tail divided by the head size (scalar Cauchy–Schwarz step of
Chen–Epperly–Tropp–Webber 2023, Thm 3.1). -/
theorem sq_max_sum_sub_tail_le_card_mul_sum_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (_hd : ∀ i, 0 ≤ d i) (S : Finset ι) {r : ℕ} (hcard : S.card ≤ r)
    {τ : ℝ} (htail : (∑ i, if i ∉ S then d i else 0) ≤ τ) :
    (max ((∑ i, d i) - τ) 0) ^ 2 ≤ (r : ℝ) * ∑ i, d i ^ 2 := by
  have hhead : (∑ i, if i ∈ S then d i else 0) = ∑ i ∈ S, d i := by
    rw [← Finset.sum_filter]
    simp
  have hsum : (∑ i, d i) = (∑ i ∈ S, d i) + ∑ i, if i ∉ S then d i else 0 := by
    rw [← hhead, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [hi]
  have hlow : (∑ i, d i) - τ ≤ ∑ i ∈ S, d i := by rw [hsum]; linarith
  have hcs : (∑ i ∈ S, d i) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, d i ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) d
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using h
  have hsq : (∑ i ∈ S, d i ^ 2) ≤ ∑ i, d i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
  have hcard' : (S.card : ℝ) ≤ r := by exact_mod_cast hcard
  have henergy : (∑ i ∈ S, d i) ^ 2 ≤ (r : ℝ) * ∑ i, d i ^ 2 :=
    hcs.trans (mul_le_mul hcard' hsq (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Nat.cast_nonneg _))
  by_cases hu : (∑ i, d i) ≤ τ
  · rw [max_eq_right (sub_nonpos.mpr hu), zero_pow two_ne_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  · rw [max_eq_left (sub_nonneg.mpr (lt_of_not_ge hu).le)]
    exact (pow_le_pow_left₀ (sub_nonneg.mpr (lt_of_not_ge hu).le) hlow 2).trans henergy

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]

/-- Summing a function of the sorted eigenvalues gives the same spectral sum as the
matrix-labelled eigenvalues, for real symmetric and complex Hermitian matrices alike
(`[RCLike 𝕜]`); Mathlib's sorted-eigenvalue convention. -/
theorem sum_eigenvalues_eq_sum_sorted {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (∑ i : n, f (hA.eigenvalues i)) = ∑ i : Fin (Fintype.card n), f (hA.eigenvalues₀ i) := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  rw [← e.sum_comp (fun i : n => f (hA.eigenvalues i))]
  simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]

/-- The **spectral trace tail** `∑_{i ≥ r} λ_i(A)` of a Hermitian matrix (sorted eigenvalues,
`0`-indexed): the optimal trace error of a rank-`r` approximation of a PSD matrix.
Chen–Epperly–Tropp–Webber 2023, §1 (`τ_r`). -/
def spectralTraceTail (A : Matrix n n 𝕜) (hA : A.IsHermitian) (r : ℕ) : ℝ :=
  ∑ i : Fin (Fintype.card n), if r ≤ (i : ℕ) then hA.eigenvalues₀ i else 0

/-- Sorted eigenvalues of a positive semidefinite matrix are nonnegative. -/
theorem eigenvalues₀_nonneg_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (i : Fin (Fintype.card n)) : 0 ≤ hA.isHermitian.eigenvalues₀ i := by
  have h := hA.eigenvalues_nonneg (Fintype.equivOfCardEq (Fintype.card_fin _) i)
  simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using h

/-- The real part of the trace is the sum of the sorted eigenvalues. -/
private theorem re_trace_eq_sum_eigenvalues₀ {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.re A.trace = ∑ i : Fin (Fintype.card n), hA.eigenvalues₀ i := by
  rw [hA.trace_eq_sum_eigenvalues, map_sum]
  simp only [RCLike.ofReal_re]
  exact sum_eigenvalues_eq_sum_sorted hA (fun x => x)

/-- The real part of the trace of the square is the sum of the squared sorted eigenvalues. -/
private theorem re_trace_mul_self_eq_sum_eigenvalues₀_sq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.re (A * A).trace = ∑ i : Fin (Fintype.card n), hA.eigenvalues₀ i ^ 2 := by
  rw [← pow_two]
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  rw [trace_conjStarAlgAut, Matrix.diagonal_pow, Matrix.trace_diagonal, map_sum]
  simp only [Pi.pow_apply, Function.comp_apply, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  exact sum_eigenvalues_eq_sum_sorted hA (fun x => x ^ 2)

/-- The spectral trace tail of a positive semidefinite matrix is nonnegative. -/
theorem spectralTraceTail_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) (r : ℕ) :
    0 ≤ spectralTraceTail A hA.isHermitian r := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact eigenvalues₀_nonneg_of_posSemidef hA i
  · exact le_rfl

/-- The sorted tail is bounded by the (real part of the) full trace of a positive
semidefinite matrix; over `ℝ`, `RCLike.re A.trace` is `A.trace` by `RCLike.re_to_real`. -/
theorem spectralTraceTail_le_trace {A : Matrix n n 𝕜} (hA : A.PosSemidef) (r : ℕ) :
    spectralTraceTail A hA.isHermitian r ≤ RCLike.re A.trace := by
  rw [re_trace_eq_sum_eigenvalues₀ hA.isHermitian]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact eigenvalues₀_nonneg_of_posSemidef hA i

/-- If the sorted spectrum of a positive semidefinite `R` is dominated by that of a
positive semidefinite `A`, then `R` has enough trace-square energy to pay the relative
trace drift above the spectral tail of `A`. The field-independent core of
`sq_max_trace_sub_spectralTraceTail_le_mul_trace_sq` (ℝ); over any `𝕜` the domination is
`Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_of_le` (Loewner monotonicity of eigenvalues).
Chen–Epperly–Tropp–Webber 2023, proof of Thm 3.1: eigenvalue monotonicity and Cauchy–Schwarz. -/
theorem sq_max_re_trace_sub_spectralTraceTail_le_of_eigenvalues₀_le
    {A R : Matrix n n 𝕜} (hA : A.PosSemidef) (hR : R.PosSemidef)
    (hle : ∀ i, hR.isHermitian.eigenvalues₀ i ≤ hA.isHermitian.eigenvalues₀ i) (r : ℕ) :
    (max (RCLike.re R.trace - spectralTraceTail A hA.isHermitian r) 0) ^ 2 ≤
      (r : ℝ) * RCLike.re (R * R).trace := by
  let d := hR.isHermitian.eigenvalues₀
  let S := (Finset.univ : Finset (Fin (Fintype.card n))).filter
    fun i : Fin (Fintype.card n) => (i : ℕ) < r
  have hd : ∀ i, 0 ≤ d i := eigenvalues₀_nonneg_of_posSemidef hR
  have hcard : S.card ≤ r := by
    have hi : S.image Fin.val ⊆ Finset.range r := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    calc S.card = (S.image Fin.val).card := (Finset.card_image_of_injective S Fin.val_injective).symm
      _ ≤ (Finset.range r).card := Finset.card_le_card hi
      _ = r := Finset.card_range r
  have htail : (∑ i, if i ∉ S then d i else 0) ≤ spectralTraceTail A hA.isHermitian r := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, spectralTraceTail]
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact hle i
    · exact le_rfl
  rw [re_trace_eq_sum_eigenvalues₀ hR.isHermitian, re_trace_mul_self_eq_sum_eigenvalues₀_sq]
  exact sq_max_sum_sub_tail_le_card_mul_sum_sq d hd S hcard htail

/-- For PSD `R ≤ A` (Loewner), `(tr R − τ_r(A))₊² ≤ r · tr(R²)`, where `τ_r(A)` is the trace
tail after the `r` largest eigenvalues (real case of
`sq_max_re_trace_sub_spectralTraceTail_le_of_eigenvalues₀_le`). Chen–Epperly–Tropp–Webber
2023 (RPCholesky), proof of Thm 3.1: eigenvalue monotonicity and Cauchy–Schwarz. -/
theorem sq_max_trace_sub_spectralTraceTail_le_mul_trace_sq
    {A R : Matrix n n ℝ} (hA : A.PosSemidef) (hR : R.PosSemidef)
    (hRA : R ≤ A) (r : ℕ) :
    (max (R.trace - spectralTraceTail A hA.isHermitian r) 0) ^ 2 ≤
      (r : ℝ) * (R * R).trace :=
  sq_max_re_trace_sub_spectralTraceTail_le_of_eigenvalues₀_le hA hR
    (Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_of_le hR.isHermitian hA.isHermitian hRA) r

/-- A zero optimal trace tail of a positive semidefinite matrix implies rank at most
the requested head size (the rank is the number of nonzero eigenvalues).
Chen–Epperly–Tropp–Webber 2023, Thm 3.1, exact-rank case. -/
theorem rank_le_of_spectralTraceTail_eq_zero {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    {r : ℕ} (ht : spectralTraceTail A hA.isHermitian r = 0) : A.rank ≤ r := by
  have hzero : ∀ j : Fin (Fintype.card n), r ≤ (j : ℕ) → hA.isHermitian.eigenvalues₀ j = 0 := by
    intro j hj
    have hn : ∀ i : Fin (Fintype.card n), 0 ≤ if r ≤ (i : ℕ) then
        hA.isHermitian.eigenvalues₀ i else 0 := by
      intro i
      split_ifs
      · exact eigenvalues₀_nonneg_of_posSemidef hA i
      · exact le_rfl
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp ht j (Finset.mem_univ j)
    simpa only [if_pos hj] using h
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let f : {i : n // hA.isHermitian.eigenvalues i ≠ 0} → Fin r := fun i =>
    ⟨(e.symm i.val).val, by
      by_contra hi
      have hz := hzero (e.symm i.val) (Nat.le_of_not_lt hi)
      apply i.property
      simpa only [Matrix.IsHermitian.eigenvalues, e] using hz⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply e.symm.injective
    apply Fin.ext
    exact congrArg (fun z : Fin r => z.val) hij
  rw [hA.isHermitian.rank_eq_card_non_zero_eigs]
  exact (Fintype.card_le_of_injective f hf).trans (Fintype.card_fin r).le

end NLAlib
