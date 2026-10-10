import NLAlib.Matrix.ComplexVariationalPrinciple
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Attained complex Courant–Fischer extrema

Quadratic values are real parts of the complex Euclidean inner product with
the matrix operator. Every positive-dimensional complex subspace has attained
inner extrema on its Euclidean unit vectors. The spectral head and tail give
the attained exact-dimensional outer extrema, with no sign or simplicity
assumptions on eigenvalues.

Source: matrix toolkit operator derivations, §2; Horn–Johnson Theorem 4.2.6.
Atlas: `courant-fischer` (complex Hermitian scope).
-/

noncomputable section
set_option autoImplicit false
open Module

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real quadratic values on the Euclidean unit vectors of a complex subspace.
Toolkit §2; Horn–Johnson Theorem 4.2.6; helper for atlas `courant-fischer`.
The unit condition uses the Euclidean norm and contains no zero-vector quotient. -/
def complexUnitQuadFormValues (A : Matrix n n ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ n)) : Set ℝ :=
  {v | ∃ x ∈ S, ‖x‖ ^ 2 = 1 ∧ v = (inner ℂ x (A.toEuclideanLin x)).re}

omit [DecidableEq n] in
private theorem exists_complex_unit_smul (S : Submodule ℂ (EuclideanSpace ℂ n))
    {x : EuclideanSpace ℂ n} (hx : x ∈ S) (hx0 : x ≠ 0) :
    ∃ u ∈ S, ‖u‖ ^ 2 = 1 ∧ ∃ r : ℝ, 0 < r ∧ x = (r : ℂ) • u := by
  let r : ℝ := ‖x‖
  have hr : 0 < r := norm_pos_iff.mpr hx0
  let u : EuclideanSpace ℂ n := ((r⁻¹ : ℝ) : ℂ) • x
  have hu : ‖u‖ = 1 := by
    have hnorm : ‖((r⁻¹ : ℝ) : ℂ)‖ = r⁻¹ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    calc
      ‖u‖ = ‖((r⁻¹ : ℝ) : ℂ)‖ * ‖x‖ := norm_smul _ _
      _ = r⁻¹ * r := by rw [hnorm]
      _ = 1 := inv_mul_cancel₀ hr.ne'
  refine ⟨u, S.smul_mem _ hx, by rw [hu]; norm_num, r, hr, ?_⟩
  simp [u, smul_smul, hr.ne']

private theorem complex_re_inner_smul_eq (A : Matrix n n ℂ)
    (x : EuclideanSpace ℂ n) (r : ℝ) :
    (inner ℂ ((r : ℂ) • x) (A.toEuclideanLin ((r : ℂ) • x))).re =
      r ^ 2 * (inner ℂ x (A.toEuclideanLin x)).re := by
  simp only [map_smul, inner_smul_left, inner_smul_right]
  simp [Complex.mul_re, sq]
  ring

omit [DecidableEq n] in
private theorem complex_norm_smul_sq_eq (x : EuclideanSpace ℂ n) (r : ℝ) :
    ‖(r : ℂ) • x‖ ^ 2 = r ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

private theorem complex_homogeneous_lower_of_unit (A : Matrix n n ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ n)) (c : ℝ)
    (h : ∀ x ∈ S, ‖x‖ ^ 2 = 1 → c ≤ (inner ℂ x (A.toEuclideanLin x)).re) :
    ∀ x ∈ S, c * ‖x‖ ^ 2 ≤ (inner ℂ x (A.toEuclideanLin x)).re := by
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨u, hu, hu1, r, hr, he⟩ := exists_complex_unit_smul S hx hx0
  rw [he, complex_re_inner_smul_eq, complex_norm_smul_sq_eq, hu1, mul_one]
  have hh := h u hu hu1
  nlinarith [sq_nonneg r]

private theorem complex_homogeneous_upper_of_unit (A : Matrix n n ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ n)) (c : ℝ)
    (h : ∀ x ∈ S, ‖x‖ ^ 2 = 1 → (inner ℂ x (A.toEuclideanLin x)).re ≤ c) :
    ∀ x ∈ S, (inner ℂ x (A.toEuclideanLin x)).re ≤ c * ‖x‖ ^ 2 := by
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨u, hu, hu1, r, hr, he⟩ := exists_complex_unit_smul S hx hx0
  rw [he, complex_re_inner_smul_eq, complex_norm_smul_sq_eq, hu1, mul_one]
  have hh := h u hu hu1
  nlinarith [sq_nonneg r]

omit [DecidableEq n] in
private theorem isCompact_complex_unit_vectors
    (S : Submodule ℂ (EuclideanSpace ℂ n)) :
    IsCompact {x : EuclideanSpace ℂ n | x ∈ S ∧ ‖x‖ ^ 2 = 1} := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · exact S.closed_of_finiteDimensional.inter
      (isClosed_eq (by fun_prop) continuous_const)
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨1, ?_⟩
    intro x hx
    nlinarith [norm_nonneg x, hx.2]

/-- Every positive-dimensional complex subspace has attained minimum and
maximum real quadratic values on its Euclidean unit vectors. No Hermitian or
definiteness hypothesis is needed for this compactness statement.
Toolkit §2; Horn–Johnson Theorem 4.2.6; helper for atlas `courant-fischer`. -/
theorem exists_isLeast_isGreatest_complexUnitQuadFormValues (A : Matrix n n ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ n)) (hS : 0 < finrank ℂ S) :
    (∃ c, IsLeast (complexUnitQuadFormValues A S) c) ∧
      ∃ c, IsGreatest (complexUnitQuadFormValues A S) c := by
  obtain ⟨x, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hS
  have hx : (x : EuclideanSpace ℂ n) ≠ 0 := by
    intro h
    apply hx0
    exact Subtype.ext h
  obtain ⟨u, hu, hu1, _⟩ := exists_complex_unit_smul S x.property hx
  have hc : Continuous (fun x : EuclideanSpace ℂ n =>
      (inner ℂ x (A.toEuclideanLin x)).re) :=
    Complex.continuous_re.comp
      (continuous_id.inner A.toEuclideanLin.continuous_of_finiteDimensional)
  have he : complexUnitQuadFormValues A S =
      (fun x => (inner ℂ x (A.toEuclideanLin x)).re) ''
        {x : EuclideanSpace ℂ n | x ∈ S ∧ ‖x‖ ^ 2 = 1} := by
    ext c
    constructor
    · rintro ⟨x, hx, hu, rfl⟩
      exact ⟨x, ⟨hx, hu⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hu⟩, rfl⟩
      exact ⟨x, hx, hu, rfl⟩
  have hcompact : IsCompact (complexUnitQuadFormValues A S) := by
    rw [he]
    exact (isCompact_complex_unit_vectors S).image hc
  have hne : (complexUnitQuadFormValues A S).Nonempty :=
    ⟨(inner ℂ u (A.toEuclideanLin u)).re, u, hu, hu1, rfl⟩
  exact ⟨hcompact.exists_isLeast hne, hcompact.exists_isGreatest hne⟩

/-- A complex spectral head of dimension exactly `k+1` attains its minimum
real unit-vector quadratic value at the `k`-th decreasing eigenvalue.
Horn–Johnson Theorem 4.2.6; toolkit §2; helper for atlas `courant-fischer`. -/
theorem exists_submodule_finrank_eq_isLeast_complexUnitQuadFormValues
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    ∃ S : Submodule ℂ (EuclideanSpace ℂ n), finrank ℂ S = (k : ℕ) + 1 ∧
      IsLeast (complexUnitQuadFormValues A S) (hA.eigenvalues₀ k) := by
  obtain ⟨S, hdim, hbound⟩ := complex_exists_submodule_finrank_eq_eigenvalues₀_mul_le hA k
  obtain ⟨⟨c, hmin⟩, _⟩ := exists_isLeast_isGreatest_complexUnitQuadFormValues A S
    (by rw [hdim]; omega)
  have hlower : ∀ x ∈ S, c * ‖x‖ ^ 2 ≤ (inner ℂ x (A.toEuclideanLin x)).re :=
    complex_homogeneous_lower_of_unit A S c (fun x hx hu => hmin.2 ⟨x, hx, hu, rfl⟩)
  have hc : c ≤ hA.eigenvalues₀ k :=
    complex_le_eigenvalues₀_of_forall_mem hA k S (by rw [hdim]) hlower
  obtain ⟨x, hx, hu, he⟩ := hmin.1
  have hb := hbound x hx
  rw [hu, mul_one, ← he] at hb
  have heq := le_antisymm hc hb
  exact ⟨S, hdim, heq ▸ hmin⟩

/-- A complex spectral tail of dimension exactly `card n-k` attains its
maximum real unit-vector quadratic value at the `k`-th decreasing eigenvalue.
Horn–Johnson Theorem 4.2.6; toolkit §2; helper for atlas `courant-fischer`. -/
theorem exists_submodule_finrank_eq_isGreatest_complexUnitQuadFormValues
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    ∃ S : Submodule ℂ (EuclideanSpace ℂ n),
      finrank ℂ S = Fintype.card n - (k : ℕ) ∧
      IsGreatest (complexUnitQuadFormValues A S) (hA.eigenvalues₀ k) := by
  obtain ⟨S, hdim, hbound⟩ :=
    complex_exists_submodule_finrank_eq_re_inner_le_eigenvalues₀_mul hA k
  obtain ⟨_, c, hmax⟩ := exists_isLeast_isGreatest_complexUnitQuadFormValues A S
    (by rw [hdim]; have := k.isLt; omega)
  have hupper : ∀ x ∈ S, (inner ℂ x (A.toEuclideanLin x)).re ≤ c * ‖x‖ ^ 2 :=
    complex_homogeneous_upper_of_unit A S c (fun x hx hu => hmax.2 ⟨x, hx, hu, rfl⟩)
  have hc : hA.eigenvalues₀ k ≤ c := complex_eigenvalues₀_le_of_forall_mem hA k S
    (by rw [hdim]; have := k.isLt; omega) hupper
  obtain ⟨x, hx, hu, he⟩ := hmax.1
  have hb := hbound x hx
  rw [hu, mul_one, ← he] at hb
  have heq := le_antisymm hb hc
  exact ⟨S, hdim, heq ▸ hmax⟩

/-- The complex Hermitian Courant–Fischer max–min formula is attained on
subspaces of complex dimension exactly `k+1`. Each inner minimum is attained
on Euclidean unit vectors, and the outer maximum is attained by a spectral head.
Horn–Johnson Theorem 4.2.6; toolkit §2 (complex Hermitian case).
atlas: courant-fischer (partial) -/
theorem isGreatest_eigenvalues₀_min_complexUnitQuadFormValues
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    IsGreatest {c : ℝ | ∃ S : Submodule ℂ (EuclideanSpace ℂ n),
      finrank ℂ S = (k : ℕ) + 1 ∧ IsLeast (complexUnitQuadFormValues A S) c}
        (hA.eigenvalues₀ k) := by
  refine ⟨exists_submodule_finrank_eq_isLeast_complexUnitQuadFormValues hA k, ?_⟩
  rintro c ⟨S, hdim, hmin⟩
  exact complex_le_eigenvalues₀_of_forall_mem hA k S (by rw [hdim])
    (complex_homogeneous_lower_of_unit A S c (fun x hx hu => hmin.2 ⟨x, hx, hu, rfl⟩))

/-- The complex Hermitian Courant–Fischer min–max formula is attained on
subspaces of complex dimension exactly `card n-k`. Each inner maximum is
attained on Euclidean unit vectors, and the outer minimum is attained by a spectral tail.
Horn–Johnson Theorem 4.2.6; toolkit §2 (complex Hermitian case).
atlas: courant-fischer (partial) -/
theorem isLeast_eigenvalues₀_max_complexUnitQuadFormValues
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    IsLeast {c : ℝ | ∃ S : Submodule ℂ (EuclideanSpace ℂ n),
      finrank ℂ S = Fintype.card n - (k : ℕ) ∧
        IsGreatest (complexUnitQuadFormValues A S) c} (hA.eigenvalues₀ k) := by
  refine ⟨exists_submodule_finrank_eq_isGreatest_complexUnitQuadFormValues hA k, ?_⟩
  rintro c ⟨S, hdim, hmax⟩
  exact complex_eigenvalues₀_le_of_forall_mem hA k S
    (by rw [hdim]; have := k.isLt; omega)
    (complex_homogeneous_upper_of_unit A S c (fun x hx hu => hmax.2 ⟨x, hx, hu, rfl⟩))

/-- Both complex Hermitian Courant–Fischer formulas have attained inner and
outer extrema, with complex subspace dimensions exactly `k+1` and `card n-k`.
The quadratic values are real parts of Euclidean inner products on unit vectors.
No eigenvalue simplicity or sign assumption is required.
Horn–Johnson Theorem 4.2.6; toolkit §2 (complex Hermitian case).
atlas: courant-fischer -/
theorem complex_eigenvalues₀_variational_extrema {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    (IsGreatest {c : ℝ | ∃ S : Submodule ℂ (EuclideanSpace ℂ n),
      finrank ℂ S = (k : ℕ) + 1 ∧ IsLeast (complexUnitQuadFormValues A S) c}
        (hA.eigenvalues₀ k)) ∧
    IsLeast {c : ℝ | ∃ S : Submodule ℂ (EuclideanSpace ℂ n),
      finrank ℂ S = Fintype.card n - (k : ℕ) ∧
        IsGreatest (complexUnitQuadFormValues A S) c} (hA.eigenvalues₀ k) :=
  ⟨isGreatest_eigenvalues₀_min_complexUnitQuadFormValues hA k,
    isLeast_eigenvalues₀_max_complexUnitQuadFormValues hA k⟩

/-- The largest complex Hermitian eigenvalue is the attained maximum of
real quadratic values on Euclidean unit vectors. Positive dimension is required
only to form the first eigenvalue index.
Horn–Johnson Theorem 4.2.6; toolkit §2 (complex Hermitian case).
atlas: courant-fischer (partial) -/
theorem isGreatest_complexUnitQuadFormValues_top {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (hn : 0 < Fintype.card n) :
    IsGreatest (complexUnitQuadFormValues A ⊤) (hA.eigenvalues₀ ⟨0, hn⟩) := by
  obtain ⟨S, hdim, hS⟩ := exists_submodule_finrank_eq_isGreatest_complexUnitQuadFormValues
    hA ⟨0, hn⟩
  have htop : S = ⊤ := Submodule.eq_top_of_finrank_eq
    (by simpa only [Fin.val_zero, Nat.sub_zero, finrank_euclideanSpace] using hdim)
  rwa [htop] at hS

/-- The smallest complex Hermitian eigenvalue is the attained minimum of
real quadratic values on Euclidean unit vectors. Empty dimension is excluded
because it has no final eigenvalue index.
Horn–Johnson Theorem 4.2.6; toolkit §2 (complex Hermitian case).
atlas: courant-fischer (partial) -/
theorem isLeast_complexUnitQuadFormValues_top {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (hn : 0 < Fintype.card n) :
    IsLeast (complexUnitQuadFormValues A ⊤)
      (hA.eigenvalues₀ ⟨Fintype.card n - 1, by omega⟩) := by
  obtain ⟨S, hdim, hS⟩ := exists_submodule_finrank_eq_isLeast_complexUnitQuadFormValues
    hA ⟨Fintype.card n - 1, by omega⟩
  change finrank ℂ S = (Fintype.card n - 1) + 1 at hdim
  have hdim' : finrank ℂ S = Fintype.card n := by omega
  have htop : S = ⊤ := Submodule.eq_top_of_finrank_eq
    (by simpa only [finrank_euclideanSpace] using hdim')
  rwa [htop] at hS

end NLAlib
