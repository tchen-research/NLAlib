import NLAlib.Matrix.ComplexRayleigh
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Complex Hermitian Courant–Fischer certificates

The quadratic value is the real part of the complex Euclidean inner product;
dimensions are taken over ℂ. The proof uses the sorted Mathlib eigenbasis and
the dimension intersection argument of toolkit §2. It keeps Mathlib's
`eigenvalues₀` and permits negative eigenvalues. Exact-dimensional witnesses
are provided for both variational halves. Atlas: `courant-fischer`.
-/

noncomputable section
open scoped Matrix
open Module

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace ComplexCourantFischer

variable {A : Matrix n n ℂ} (hA : A.IsHermitian)

private def restrictedCoordinates {p : ℕ} (f : Fin p → Fin (Fintype.card n)) :
    EuclideanSpace ℂ n →ₗ[ℂ] (Fin p → ℂ) where
  toFun x i := complexEigenvectorCoordinates hA x (f i)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

private def hiCoordinates (k : Fin (Fintype.card n)) :
    EuclideanSpace ℂ n →ₗ[ℂ] (Fin (Fintype.card n - ((k : ℕ) + 1)) → ℂ) :=
  restrictedCoordinates hA fun j => ⟨(k : ℕ) + 1 + j, by have := j.isLt; omega⟩

private def loCoordinates (k : Fin (Fintype.card n)) :
    EuclideanSpace ℂ n →ₗ[ℂ] (Fin (k : ℕ) → ℂ) :=
  restrictedCoordinates hA fun j => ⟨j, by have := j.isLt; have := k.isLt; omega⟩

private theorem coord_of_hiCoordinates (k : Fin (Fintype.card n))
    {x : EuclideanSpace ℂ n} (hx : hiCoordinates hA k x = 0)
    (j : Fin (Fintype.card n)) (hj : k < j) :
    complexEigenvectorCoordinates hA x j = 0 := by
  have h := congrFun hx ⟨(j : ℕ) - ((k : ℕ) + 1), by have := j.isLt; omega⟩
  have he : (⟨(k : ℕ) + 1 + ((j : ℕ) - ((k : ℕ) + 1)), by omega⟩ :
      Fin (Fintype.card n)) = j := by ext; simp only; omega
  simpa [hiCoordinates, restrictedCoordinates, he] using h

private theorem coord_of_loCoordinates (k : Fin (Fintype.card n))
    {x : EuclideanSpace ℂ n} (hx : loCoordinates hA k x = 0)
    (j : Fin (Fintype.card n)) (hj : j < k) :
    complexEigenvectorCoordinates hA x j = 0 := by
  have h := congrFun hx ⟨j, hj⟩
  simpa [loCoordinates, restrictedCoordinates] using h

private theorem eigenvalues₀_mul_le_of_coord (k : Fin (Fintype.card n))
    {x : EuclideanSpace ℂ n}
    (hx : ∀ j, k < j → complexEigenvectorCoordinates hA x j = 0) :
    hA.eigenvalues₀ k * ‖x‖ ^ 2 ≤ (inner ℂ x (A.toEuclideanLin x)).re := by
  rw [re_inner_euclideanLin_eq_sum hA, ← sum_norm_sq_complexEigenvectorCoordinates hA x,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rcases le_or_gt j k with hjk | hjk
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone hjk) (sq_nonneg _)
  · simp [hx j hjk]

private theorem re_inner_le_eigenvalues₀_mul_of_coord (k : Fin (Fintype.card n))
    {x : EuclideanSpace ℂ n}
    (hx : ∀ j, j < k → complexEigenvectorCoordinates hA x j = 0) :
    (inner ℂ x (A.toEuclideanLin x)).re ≤ hA.eigenvalues₀ k * ‖x‖ ^ 2 := by
  rw [re_inner_euclideanLin_eq_sum hA, ← sum_norm_sq_complexEigenvectorCoordinates hA x,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rcases lt_or_ge j k with hjk | hjk
  · simp [hx j hjk]
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone hjk) (sq_nonneg _)

omit [DecidableEq n] in
private theorem exists_mem_ne_zero_map_eq_zero {p : ℕ}
    (f : EuclideanSpace ℂ n →ₗ[ℂ] (Fin p → ℂ))
    (W : Submodule ℂ (EuclideanSpace ℂ n)) (hW : p < finrank ℂ W) :
    ∃ x ∈ W, x ≠ 0 ∧ f x = 0 := by
  have hker : LinearMap.ker (f.domRestrict W) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rwa [Module.finrank_fin_fun])
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨y, y.property, fun h => hy0 (Subtype.ext h), hy⟩

omit [DecidableEq n] in
private theorem card_le_finrank_ker_add {p : ℕ}
    (f : EuclideanSpace ℂ n →ₗ[ℂ] (Fin p → ℂ)) :
    Fintype.card n ≤ finrank ℂ (LinearMap.ker f) + p := by
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hr : finrank ℂ (LinearMap.range f) ≤ p := by
    simpa using (LinearMap.range f).finrank_le
  rw [finrank_euclideanSpace] at h
  omega

omit [Fintype n] [DecidableEq n] in
private theorem exists_submodule_le_finrank_eq (S : Submodule ℂ (EuclideanSpace ℂ n))
    (d : ℕ) (hd : d ≤ finrank ℂ S) :
    ∃ T : Submodule ℂ (EuclideanSpace ℂ n), T ≤ S ∧ finrank ℂ T = d := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hd
  have hf := hv.map' S.subtype (Submodule.ker_subtype S)
  refine ⟨Submodule.span ℂ (Set.range fun i : Fin d => (v i : EuclideanSpace ℂ n)), ?_, ?_⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (v i).property
  · change finrank ℂ (Submodule.span ℂ (Set.range (S.subtype ∘ v))) = d
    simpa only [Fintype.card_fin] using finrank_span_eq_card hf

end ComplexCourantFischer

open ComplexCourantFischer

/-- The complex Hermitian min–max threshold: an upper quadratic bound on a
subspace of codimension at most `k` bounds the `k`-th largest eigenvalue.
Horn–Johnson Theorem 4.2.6; toolkit §2; helpers for `courant-fischer`.
Dimensions are over ℂ and the ordered quadratic value is its real part. -/
theorem complex_eigenvalues₀_le_of_forall_mem {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) (W : Submodule ℂ (EuclideanSpace ℂ n))
    (hW : Fintype.card n ≤ finrank ℂ W + (k : ℕ)) {c : ℝ}
    (hAW : ∀ x ∈ W, (inner ℂ x (A.toEuclideanLin x)).re ≤ c * ‖x‖ ^ 2) :
    hA.eigenvalues₀ k ≤ c := by
  obtain ⟨x, hxW, hx0, hx⟩ := exists_mem_ne_zero_map_eq_zero (hiCoordinates hA k) W
    (by have := k.isLt; omega)
  have h1 := eigenvalues₀_mul_le_of_coord hA k (coord_of_hiCoordinates hA k hx)
  have h2 := hAW x hxW
  exact le_of_mul_le_mul_right (h1.trans h2) (pow_pos (norm_pos_iff.mpr hx0) 2)

/-- The complex Hermitian max–min threshold on a subspace of dimension at
least `k+1`. Horn–Johnson Theorem 4.2.6; toolkit §2; helper for `courant-fischer`.
No positivity condition on the eigenvalue or threshold is needed. -/
theorem complex_le_eigenvalues₀_of_forall_mem {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) (S : Submodule ℂ (EuclideanSpace ℂ n))
    (hS : (k : ℕ) + 1 ≤ finrank ℂ S) {c : ℝ}
    (hAS : ∀ x ∈ S, c * ‖x‖ ^ 2 ≤ (inner ℂ x (A.toEuclideanLin x)).re) :
    c ≤ hA.eigenvalues₀ k := by
  obtain ⟨x, hxS, hx0, hx⟩ := exists_mem_ne_zero_map_eq_zero (loCoordinates hA k) S (by omega)
  have h1 := re_inner_le_eigenvalues₀_mul_of_coord hA k (coord_of_loCoordinates hA k hx)
  have h2 := hAS x hxS
  exact le_of_mul_le_mul_right (h2.trans h1) (pow_pos (norm_pos_iff.mpr hx0) 2)

/-- Exact-dimensional attaining spectral head for complex Hermitian matrices.
Horn–Johnson Theorem 4.2.6; toolkit §2; helper for `courant-fischer`.
The subspace has complex dimension `k+1`. -/
theorem complex_exists_submodule_finrank_eq_eigenvalues₀_mul_le {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    ∃ S : Submodule ℂ (EuclideanSpace ℂ n), finrank ℂ S = (k : ℕ) + 1 ∧
      ∀ x ∈ S, hA.eigenvalues₀ k * ‖x‖ ^ 2 ≤ (inner ℂ x (A.toEuclideanLin x)).re := by
  let W := LinearMap.ker (hiCoordinates hA k)
  have hdim : (k : ℕ) + 1 ≤ finrank ℂ W := by
    have h := card_le_finrank_ker_add (hiCoordinates hA k)
    have := k.isLt
    dsimp [W]
    omega
  obtain ⟨S, hSW, hS⟩ := exists_submodule_le_finrank_eq W ((k : ℕ) + 1) hdim
  refine ⟨S, hS, fun x hx => eigenvalues₀_mul_le_of_coord hA k ?_⟩
  exact coord_of_hiCoordinates hA k (hSW hx)

/-- Exact-dimensional attaining spectral tail for complex Hermitian matrices.
Horn–Johnson Theorem 4.2.6; toolkit §2; helper for `courant-fischer`.
The subspace has complex dimension `card n-k`. -/
theorem complex_exists_submodule_finrank_eq_re_inner_le_eigenvalues₀_mul {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    ∃ S : Submodule ℂ (EuclideanSpace ℂ n), finrank ℂ S = Fintype.card n - (k : ℕ) ∧
      ∀ x ∈ S, (inner ℂ x (A.toEuclideanLin x)).re ≤ hA.eigenvalues₀ k * ‖x‖ ^ 2 := by
  let W := LinearMap.ker (loCoordinates hA k)
  have hdim : Fintype.card n - (k : ℕ) ≤ finrank ℂ W := by
    have h := card_le_finrank_ker_add (loCoordinates hA k)
    dsimp [W]
    omega
  obtain ⟨S, hSW, hS⟩ := exists_submodule_le_finrank_eq W (Fintype.card n - (k : ℕ)) hdim
  refine ⟨S, hS, fun x hx => re_inner_le_eigenvalues₀_mul_of_coord hA k ?_⟩
  exact coord_of_loCoordinates hA k (hSW hx)

end NLAlib
