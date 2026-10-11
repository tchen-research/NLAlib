import NLAlib.Matrix.ComplexVariationalPrinciple
import NLAlib.Matrix.TraceTail
import NLAlib.Matrix.TracePowers

/-!
# Native complex spectral trace tails

The actual real complex trace and sorted Hermitian spectrum supply the trace-square
energy and zero-tail rank bounds for complex RPCholesky. Source: manuscript
`sa:rp-recursion`, `sa:rp-theorem`, and the complex audit Part VII.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Native complex Hermitian eigenvalues are monotone under PSD order.
Source: complex Courant--Fischer; supports manuscript `sa:rp-recursion`. -/
theorem complex_eigenvalues₀_le_eigenvalues₀_of_posSemidef_sub
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : (B - A).PosSemidef) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  obtain ⟨S, hS, hAS⟩ := complex_exists_submodule_finrank_eq_eigenvalues₀_mul_le hA k
  refine complex_le_eigenvalues₀_of_forall_mem hB k S hS.ge fun x hx => (hAS x hx).trans ?_
  have h0 := h.re_dotProduct_nonneg (WithLp.ofLp x)
  have he : ∀ M : Matrix n n ℂ,
      (inner ℂ x (M.toEuclideanLin x)).re =
        (star (WithLp.ofLp x) ⬝ᵥ (M *ᵥ WithLp.ofLp x)).re := by
    intro M
    change (inner ℂ (WithLp.toLp 2 (WithLp.ofLp x))
      (WithLp.toLp 2 (M *ᵥ WithLp.ofLp x))).re = _
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rw [he, he]
  change 0 ≤ (star x.ofLp ⬝ᵥ ((B - A) *ᵥ x.ofLp)).re at h0
  simp only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at h0
  linarith

/-- Real complex traces of powers equal real eigenvalue power sums.
Source: finite complex spectral theorem; manuscript `sa:rp-recursion`. -/
theorem complex_re_trace_pow_eq_sum_eigenvalues {R : Matrix n n ℂ}
    (hR : R.IsHermitian) (j : ℕ) : (R ^ j).trace.re = ∑ i, hR.eigenvalues i ^ j := by
  conv_lhs => rw [hR.spectral_theorem, ← map_pow]
  rw [trace_conjStarAlgAut_complex, Matrix.diagonal_pow, Matrix.trace_diagonal,
    Complex.re_sum]
  change (∑ i, ((hR.eigenvalues i : ℂ) ^ j).re) = _
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
/-- Summing a function of the sorted eigenvalues gives the same spectral sum as the
matrix-labelled eigenvalues. Source: Mathlib's spectral ordering convention;
manuscript `sa:rp-recursion`, ordered trace sums. -/
theorem complex_sum_eigenvalues_eq_sum_sorted {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (∑ i : n, f (hA.eigenvalues i)) = ∑ i : Fin (Fintype.card n), f (hA.eigenvalues₀ i) := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  rw [← e.sum_comp (fun i : n => f (hA.eigenvalues i))]
  simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]

/-- The zero-indexed sorted eigenvalue tail of a Hermitian matrix.
Source: manuscript `sa:rpcholesky`, its optimal trace tail `tau_*`. -/
def complexSpectralTraceTail (A : Matrix n n ℂ) (hA : A.IsHermitian) (r : ℕ) : ℝ :=
  ∑ i : Fin (Fintype.card n), if r ≤ (i : ℕ) then hA.eigenvalues₀ i else 0

/-- Sorted eigenvalues of a positive semidefinite matrix are nonnegative.
Source: Mathlib's spectral theorem; manuscript `sa:rp-recursion`. -/
theorem complex_eigenvalues₀_nonneg_of_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (i : Fin (Fintype.card n)) : 0 ≤ hA.isHermitian.eigenvalues₀ i := by
  have h := hA.eigenvalues_nonneg (Fintype.equivOfCardEq (Fintype.card_fin _) i)
  simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using h

/-- The sorted trace tail of a positive semidefinite matrix is nonnegative.
Source: manuscript `sa:rpcholesky`, optimal nonnegative trace tail. -/
theorem complexSpectralTraceTail_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) (r : ℕ) :
    0 ≤ complexSpectralTraceTail A hA.isHermitian r := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact complex_eigenvalues₀_nonneg_of_posSemidef hA i
  · exact le_rfl

/-- The sorted tail is bounded by the full trace of a positive semidefinite matrix.
Source: manuscript `sa:rpcholesky`, relative optimal tail normalization. -/
theorem complexSpectralTraceTail_le_trace {A : Matrix n n ℂ} (hA : A.PosSemidef) (r : ℕ) :
    complexSpectralTraceTail A hA.isHermitian r ≤ A.trace.re := by
  have ht : A.trace.re = ∑ i : Fin (Fintype.card n), hA.isHermitian.eigenvalues₀ i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp only [← RCLike.re_eq_complex_re, RCLike.ofReal_re]
    exact complex_sum_eigenvalues_eq_sum_sorted hA.isHermitian (fun x => x)
  rw [ht]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact complex_eigenvalues₀_nonneg_of_posSemidef hA i

/-- A Loewner-bounded positive semidefinite residual has enough trace-square energy
to pay the exact relative trace drift. Source: manuscript `sa:rp-recursion`;
CETW (2025), eigenvalue monotonicity and Cauchy--Schwarz.
The sorted tail and zero trace cases are explicit. -/
theorem complex_sq_max_trace_sub_spectralTraceTail_le_mul_trace_sq
    {A R : Matrix n n ℂ} (hA : A.PosSemidef) (hR : R.PosSemidef)
    (hAR : (A - R).PosSemidef) (r : ℕ) :
    (max (R.trace.re - complexSpectralTraceTail A hA.isHermitian r) 0) ^ 2 ≤
      (r : ℝ) * (R * R).trace.re := by
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
  have htail : (∑ i, if i ∉ S then d i else 0) ≤ complexSpectralTraceTail A hA.isHermitian r := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, complexSpectralTraceTail]
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact complex_eigenvalues₀_le_eigenvalues₀_of_posSemidef_sub hR.isHermitian hA.isHermitian hAR i
    · exact le_rfl
  have ht : R.trace.re = ∑ i, d i := by
    rw [hR.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp only [← RCLike.re_eq_complex_re, RCLike.ofReal_re]
    exact complex_sum_eigenvalues_eq_sum_sorted hR.isHermitian (fun x => x)
  have hs : (R * R).trace.re = ∑ i, d i ^ 2 := by
    rw [← pow_two, complex_re_trace_pow_eq_sum_eigenvalues hR.isHermitian]
    exact complex_sum_eigenvalues_eq_sum_sorted hR.isHermitian (fun x => x ^ 2)
  rw [ht, hs]
  exact sq_max_sum_sub_tail_le_card_mul_sum_sq d hd S hcard htail

/-- A zero optimal trace tail of a positive semidefinite matrix implies rank at most
the requested head size. Source: manuscript `sa:rp-theorem`, exact-rank branch;
the rank equals the number of nonzero eigenvalues. -/
theorem complex_rank_le_of_spectralTraceTail_eq_zero {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {r : ℕ} (ht : complexSpectralTraceTail A hA.isHermitian r = 0) : A.rank ≤ r := by
  have hzero : ∀ j : Fin (Fintype.card n), r ≤ (j : ℕ) → hA.isHermitian.eigenvalues₀ j = 0 := by
    intro j hj
    have hn : ∀ i : Fin (Fintype.card n), 0 ≤ if r ≤ (i : ℕ) then
        hA.isHermitian.eigenvalues₀ i else 0 := by
      intro i
      split_ifs
      · exact complex_eigenvalues₀_nonneg_of_posSemidef hA i
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
