import NLAlib.Matrix.CourantFischer
import NLAlib.Matrix.InversePowerLimit
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Trace-square lower bounds from an upper spectral tail

Loewner eigenvalue monotonicity and finite Cauchy--Schwarz give the scalar
energy lower bound used by randomly pivoted Cholesky.
Source: manuscript `sa:rp-recursion`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- A nonnegative finite sequence has squared energy at least the squared excess
above its complementary tail divided by the head size. Source: manuscript
`sa:rp-recursion`, scalar Cauchy--Schwarz step. -/
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

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Summing a function of the sorted eigenvalues gives the same spectral sum as the
matrix-labelled eigenvalues. Source: Mathlib's spectral ordering convention;
manuscript `sa:rp-recursion`, ordered trace sums. -/
theorem sum_eigenvalues_eq_sum_sorted {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (∑ i : n, f (hA.eigenvalues i)) = ∑ i : Fin (Fintype.card n), f (hA.eigenvalues₀ i) := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  rw [← e.sum_comp (fun i : n => f (hA.eigenvalues i))]
  simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]

/-- The zero-indexed sorted eigenvalue tail of a Hermitian matrix.
Source: manuscript `sa:rpcholesky`, its optimal trace tail `tau_*`. -/
def spectralTraceTail (A : Matrix n n ℝ) (hA : A.IsHermitian) (r : ℕ) : ℝ :=
  ∑ i : Fin (Fintype.card n), if r ≤ (i : ℕ) then hA.eigenvalues₀ i else 0

/-- Sorted eigenvalues of a positive semidefinite matrix are nonnegative.
Source: Mathlib's spectral theorem; manuscript `sa:rp-recursion`. -/
theorem eigenvalues₀_nonneg_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (i : Fin (Fintype.card n)) : 0 ≤ hA.isHermitian.eigenvalues₀ i := by
  have h := hA.eigenvalues_nonneg (Fintype.equivOfCardEq (Fintype.card_fin _) i)
  simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using h

/-- The sorted trace tail of a positive semidefinite matrix is nonnegative.
Source: manuscript `sa:rpcholesky`, optimal nonnegative trace tail. -/
theorem spectralTraceTail_nonneg {A : Matrix n n ℝ} (hA : A.PosSemidef) (r : ℕ) :
    0 ≤ spectralTraceTail A hA.isHermitian r := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact eigenvalues₀_nonneg_of_posSemidef hA i
  · exact le_rfl

/-- The sorted tail is bounded by the full trace of a positive semidefinite matrix.
Source: manuscript `sa:rpcholesky`, relative optimal tail normalization. -/
theorem spectralTraceTail_le_trace {A : Matrix n n ℝ} (hA : A.PosSemidef) (r : ℕ) :
    spectralTraceTail A hA.isHermitian r ≤ A.trace := by
  have ht : A.trace = ∑ i : Fin (Fintype.card n), hA.isHermitian.eigenvalues₀ i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    exact sum_eigenvalues_eq_sum_sorted hA.isHermitian (fun x => x)
  rw [ht]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact eigenvalues₀_nonneg_of_posSemidef hA i

/-- A Loewner-bounded positive semidefinite residual has enough trace-square energy
to pay the exact relative trace drift. Source: manuscript `sa:rp-recursion`;
CETW (2025), eigenvalue monotonicity and Cauchy--Schwarz.
The sorted tail and zero trace cases are explicit. -/
theorem sq_max_trace_sub_spectralTraceTail_le_mul_trace_sq
    {A R : Matrix n n ℝ} (hA : A.PosSemidef) (hR : R.PosSemidef)
    (hAR : (A - R).PosSemidef) (r : ℕ) :
    (max (R.trace - spectralTraceTail A hA.isHermitian r) 0) ^ 2 ≤
      (r : ℝ) * (R * R).trace := by
  let d := hR.isHermitian.eigenvalues₀
  let S := (Finset.univ : Finset (Fin (Fintype.card n))).filter
    fun i : Fin (Fintype.card n) => (i : ℕ) < r
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    have h := hR.eigenvalues_nonneg (Fintype.equivOfCardEq (Fintype.card_fin _) i)
    simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using h
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
    · exact eigenvalues₀_le_eigenvalues₀_of_posSemidef_sub hR.isHermitian hA.isHermitian hAR i
    · exact le_rfl
  have ht : R.trace = ∑ i, d i := by
    rw [hR.isHermitian.trace_eq_sum_eigenvalues]
    exact sum_eigenvalues_eq_sum_sorted hR.isHermitian (fun x => x)
  have hs : (R * R).trace = ∑ i, d i ^ 2 := by
    rw [← pow_two, trace_pow_eq_sum_eigenvalues hR.isHermitian]
    exact sum_eigenvalues_eq_sum_sorted hR.isHermitian (fun x => x ^ 2)
  rw [ht, hs]
  exact sq_max_sum_sub_tail_le_card_mul_sum_sq d hd S hcard htail

/-- A zero optimal trace tail of a positive semidefinite matrix implies rank at most
the requested head size. Source: manuscript `sa:rp-theorem`, exact-rank branch;
the rank equals the number of nonzero eigenvalues. -/
theorem rank_le_of_spectralTraceTail_eq_zero {A : Matrix n n ℝ} (hA : A.PosSemidef)
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
