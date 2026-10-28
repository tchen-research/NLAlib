import NLAlib.Krylov.Solvers.GMRESOrthogonality

/-!
# Coordinate geometry for arbitrary GMRES convergence curves

If `Ab,A²b,...` are consecutive coordinate vectors, GMRES removes precisely
the corresponding initial coordinates of `b`. This is a native complex GMRES
statement, including stagnation of individual residual norms.
Source: Greenbaum--Pták--Strakoš (1996), constructive proof.
-/

noncomputable section
open scoped Matrix
open Matrix Finset
namespace NLAlib

/-- The initial `k` coordinates of a vector, zero elsewhere. -/
def coordinateHead {n : ℕ} (b : Fin n → ℂ) (k : ℕ) : Fin n → ℂ :=
  fun i => if i.val < k then b i else 0

/-- A sum of the first `k` coordinate vectors is coordinate truncation. -/
theorem sum_smul_coordinate_eq_head {n k : ℕ} (b : Fin n → ℂ) (hk : k ≤ n) :
    (∑ j : Fin k, b ⟨j.val,lt_of_lt_of_le j.isLt hk⟩ •
      Pi.single ⟨j.val,lt_of_lt_of_le j.isLt hk⟩ (1 : ℂ)) = coordinateHead b k := by
  funext i
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,coordinateHead]
  by_cases hi : i.val < k
  · rw [if_pos hi]
    rw [sum_eq_single (⟨i.val,hi⟩ : Fin k)]
    · simp
    · intro j _ hji
      have hn : (⟨j.val,lt_of_lt_of_le j.isLt hk⟩ : Fin n) ≠ i := by
        intro he
        apply hji
        apply Fin.ext
        exact congrArg (fun t : Fin n => t.val) he
      simp [Ne.symm hn]
    · simp
  · rw [if_neg hi]
    apply sum_eq_zero
    intro j _
    have hn : (⟨j.val,lt_of_lt_of_le j.isLt hk⟩ : Fin n) ≠ i := by
      intro he
      exact hi (by simpa only [← congrArg Fin.val he] using j.isLt)
    simp [Ne.symm hn]

/-- The explicit Krylov correction that removes the first coordinates. -/
def gmresCurveCorrection {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ)
    (k : ℕ) (hk : k ≤ n) : Fin n → ℂ :=
  ∑ j : Fin k, b ⟨j.val,lt_of_lt_of_le j.isLt hk⟩ • (A^j.val *ᵥ b)

/-- The correction belongs to the native Krylov space. -/
theorem gmresCurveCorrection_mem {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) (hk : k ≤ n) : gmresCurveCorrection A b k hk ∈ krylovSpace A b k := by
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨j,rfl⟩

/-- The assumed consecutive powers give exactly the coordinate-head correction. -/
theorem mulVec_gmresCurveCorrection {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) (hk : k < n)
    (hs : ∀ j : Fin (n-1), A^(j.val+1) *ᵥ b =
      Pi.single ⟨j.val,by have := j.isLt; omega⟩ (1 : ℂ)) :
    A *ᵥ gmresCurveCorrection A b k hk.le = coordinateHead b k := by
  unfold gmresCurveCorrection
  rw [Matrix.mulVec_sum]
  have he (j : Fin k) : A *ᵥ (A^j.val *ᵥ b) =
      Pi.single ⟨j.val,lt_of_lt_of_le j.isLt hk.le⟩ (1 : ℂ) := by
    rw [Matrix.mulVec_mulVec,← pow_succ']
    exact hs ⟨j.val,by have := j.isLt; omega⟩
  simp_rw [Matrix.mulVec_smul,he]
  exact sum_smul_coordinate_eq_head b hk.le

/-- The image of the native Krylov space is supported on the first coordinates. -/
theorem mulVec_eq_zero_of_coordinate_shift {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) (hk : k < n)
    (hs : ∀ j : Fin (n-1), A^(j.val+1) *ᵥ b =
      Pi.single ⟨j.val,by have := j.isLt; omega⟩ (1 : ℂ))
    {z : Fin n → ℂ} (hz : z ∈ krylovSpace A b k) (i : Fin n) (hi : k ≤ i.val) :
    (A *ᵥ z) i = 0 := by
  obtain ⟨v,hv⟩ := (range_krylovMatrix A b k).symm ▸ hz
  change krylovMatrix A b k *ᵥ v = z at hv
  rw [← hv,Matrix.mulVec_mulVec]
  change ∑ j : Fin k, (A*krylovMatrix A b k) i j*v j = 0
  apply sum_eq_zero
  intro j _
  rw [mul_krylovMatrix_apply]
  have he := hs ⟨j.val,by have := j.isLt; omega⟩
  have hn : i ≠ (⟨j.val,by have := j.isLt; omega⟩ : Fin n) := by
    intro heq
    have hval : i.val = j.val := congrArg (fun t : Fin n => t.val) heq
    have := j.isLt
    omega
  simp only [he,Pi.single_apply,if_neg hn,zero_mul]

/-- The explicit correction is a native complex GMRES iterate, proved through
the Hermitian Petrov--Galerkin condition.
atlas: gmres-any-convergence-curve (partial) -/
theorem isGMRESIterate_gmresCurveCorrection {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (hk : k < n)
    (hs : ∀ j : Fin (n-1), A^(j.val+1) *ᵥ b =
      Pi.single ⟨j.val,by have := j.isLt; omega⟩ (1 : ℂ)) :
    IsGMRESIterate A b 0 k (gmresCurveCorrection A b k hk.le) := by
  apply isGMRESIterate_iff_forall_star_dotProduct_eq_zero.mpr
  simp only [Matrix.mulVec_zero,sub_zero]
  refine ⟨gmresCurveCorrection_mem A b hk.le,?_⟩
  intro z hz
  rw [mulVec_gmresCurveCorrection A b hk hs]
  apply sum_eq_zero
  intro i _
  by_cases hi : i.val < k
  · simp [coordinateHead,hi]
  · have he := mulVec_eq_zero_of_coordinate_shift A b hk hs hz i (Nat.le_of_not_gt hi)
    simp only [Pi.star_apply,he,star_zero,zero_mul]

/-- Every native GMRES minimizer has the coordinate-tail residual under the
consecutive-coordinate-power construction.
atlas: gmres-any-convergence-curve (partial) -/
theorem IsGMRESIterate.residual_eq_coordinate_tail {n k : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} {b x : Fin n → ℂ} (hx : IsGMRESIterate A b 0 k x)
    (hk : k < n)
    (hs : ∀ j : Fin (n-1), A^(j.val+1) *ᵥ b =
      Pi.single ⟨j.val,by have := j.isLt; omega⟩ (1 : ℂ)) :
    b-A *ᵥ x = b-coordinateHead b k := by
  rw [hx.residual_eq (isGMRESIterate_gmresCurveCorrection A b hk hs),
    mulVec_gmresCurveCorrection A b hk hs]

end NLAlib
