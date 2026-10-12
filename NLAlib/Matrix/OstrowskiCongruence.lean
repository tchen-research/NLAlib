import NLAlib.Matrix.EigenvalueOrder
import NLAlib.Matrix.SigmaMinTransport
import NLAlib.Matrix.SingularValueInvariance
import NLAlib.ForMathlib.LinearAlgebra.ComapDimension

/-!
# Ostrowski's eigenvalue theorem under congruence

Rayleigh subspaces pulled back through the transposed transformation give
the sharp signed lower and upper scaling bounds, even when the transformation
is singular. Each sorted eigenvalue is therefore scaled by a number between
the squared extreme singular values. Positive and negative spectral counts
cannot increase. Source: Horn--Johnson (2013), Theorem 4.5.9 and Corollary 4.5.11.
Atlas: `ostrowski-congruence-eigenvalues`.
-/

noncomputable section
open Matrix Module

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The smallest singular value of a nonempty square matrix is preserved
by transposition. Singular-value invariance; helper for
`ostrowski-congruence-eigenvalues`. -/
theorem sigmaMin_transpose_eq (S : Matrix n n ℝ) (hn : 0 < Fintype.card n) :
    sigmaMin Sᵀ = sigmaMin S := by
  rw [sigmaMin_eq_toEuclideanLin_singularValues_last Sᵀ hn,
    sigmaMin_eq_toEuclideanLin_singularValues_last S hn,
    toEuclideanLin_singularValues_transpose]

omit [DecidableEq n] in
/-- The homogeneous lower squared-length bound for a matrix uses its
smallest singular value. Variational singular-value characterization;
helper for `ostrowski-congruence-eigenvalues`. -/
theorem sq_sigmaMin_mul_dotProduct_le_mulVec_dotProduct (S : Matrix n n ℝ) (x : n → ℝ) :
    sigmaMin S ^ 2 * (x ⬝ᵥ x) ≤ (S *ᵥ x) ⬝ᵥ (S *ᵥ x) := by
  have h := sigmaMin_mul_sqrt_le S x
  have h₂ := pow_le_pow_left₀
    (mul_nonneg (sigmaMin_nonneg S) (Real.sqrt_nonneg _)) h 2
  simpa only [mul_pow, Real.sq_sqrt (dotProduct_self_nonneg x),
    Real.sq_sqrt (dotProduct_self_nonneg (S *ᵥ x))] using h₂

omit [DecidableEq n] in
/-- Congruence evaluates the original quadratic form at the transposed
image of a vector. Horn--Johnson (2013), Theorem 4.5.9;
helper for `ostrowski-congruence-eigenvalues`. -/
theorem quadForm_mul_mul_transpose (S A : Matrix n n ℝ) (x : n → ℝ) :
    quadForm (S * A * Sᵀ) x = quadForm A (Sᵀ *ᵥ x) := by
  simp only [quadForm, ← Matrix.mulVec_mulVec]
  calc
    _ = (A *ᵥ (Sᵀ *ᵥ x)) ⬝ᵥ (Sᵀ *ᵥ x) := by
      simpa only [Matrix.transpose_transpose] using
        Matrix.dotProduct_transpose_mulVec Sᵀ x (A *ᵥ (Sᵀ *ᵥ x))
    _ = _ := dotProduct_comm _ _

/-- At a nonnegative original eigenvalue, congruence scales between the
squared smallest and largest singular values. Singular transformations
are included. Horn--Johnson (2013), Theorem 4.5.9.
atlas: ostrowski-congruence-eigenvalues (partial) -/
theorem eigenvalues₀_congruence_bounds_of_nonneg {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (S : Matrix n n ℝ) (k : Fin (Fintype.card n))
    (hk : 0 ≤ hA.eigenvalues₀ k) :
    sigmaMin S ^ 2 * hA.eigenvalues₀ k ≤
      (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k ∧
    (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k ≤
      specNorm S ^ 2 * hA.eigenvalues₀ k := by
  have hn : 0 < Fintype.card n := (Nat.zero_le k.val).trans_lt k.isLt
  have hlo (x : n → ℝ) : sigmaMin S ^ 2 * (x ⬝ᵥ x) ≤
      (Sᵀ *ᵥ x) ⬝ᵥ (Sᵀ *ᵥ x) := by
    simpa only [sigmaMin_transpose_eq S hn] using
      sq_sigmaMin_mul_dotProduct_le_mulVec_dotProduct Sᵀ x
  have hup (x : n → ℝ) : (Sᵀ *ᵥ x) ⬝ᵥ (Sᵀ *ᵥ x) ≤
      specNorm S ^ 2 * (x ⬝ᵥ x) := by
    simpa only [specNorm_transpose, dotProduct, pow_two] using sum_sq_mulVec_le_specNorm_sq Sᵀ x
  constructor
  · obtain ⟨V, hV, hAV⟩ := exists_submodule_eigenvalues₀_mul_le hA k
    have hdim := finrank_le_finrank_comap_endomorphism V Sᵀ.mulVecLin
    apply le_eigenvalues₀_of_forall_mem
      (Matrix.isHermitian_mul_mul_conjTranspose S hA) k (V.comap Sᵀ.mulVecLin) (by omega)
    intro x hx
    change Sᵀ *ᵥ x ∈ V at hx
    change _ ≤ quadForm (S * A * Sᵀ) x
    rw [quadForm_mul_mul_transpose]
    calc
      _ = hA.eigenvalues₀ k * (sigmaMin S ^ 2 * (x ⬝ᵥ x)) := by ring
      _ ≤ hA.eigenvalues₀ k * ((Sᵀ *ᵥ x) ⬝ᵥ (Sᵀ *ᵥ x)) :=
        mul_le_mul_of_nonneg_left (hlo x) hk
      _ ≤ _ := hAV _ hx
  · obtain ⟨W, hW, hAW⟩ := exists_submodule_le_eigenvalues₀_mul hA k
    have hdim := finrank_le_finrank_comap_endomorphism W Sᵀ.mulVecLin
    apply eigenvalues₀_le_of_forall_mem
      (Matrix.isHermitian_mul_mul_conjTranspose S hA) k (W.comap Sᵀ.mulVecLin) (by omega)
    intro x hx
    change Sᵀ *ᵥ x ∈ W at hx
    change quadForm (S * A * Sᵀ) x ≤ _
    rw [quadForm_mul_mul_transpose]
    calc
      _ ≤ hA.eigenvalues₀ k * ((Sᵀ *ᵥ x) ⬝ᵥ (Sᵀ *ᵥ x)) := hAW _ hx
      _ ≤ hA.eigenvalues₀ k * (specNorm S ^ 2 * (x ⬝ᵥ x)) :=
        mul_le_mul_of_nonneg_left (hup x) hk
      _ = _ := by ring

/-- At a nonpositive original eigenvalue, congruence reverses the two
extreme-singular-value scaling bounds. Horn--Johnson (2013), Theorem 4.5.9.
atlas: ostrowski-congruence-eigenvalues (partial) -/
theorem eigenvalues₀_congruence_bounds_of_nonpos {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (S : Matrix n n ℝ) (k : Fin (Fintype.card n))
    (hk : hA.eigenvalues₀ k ≤ 0) :
    specNorm S ^ 2 * hA.eigenvalues₀ k ≤
      (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k ∧
    (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k ≤
      sigmaMin S ^ 2 * hA.eigenvalues₀ k := by
  have hn : 0 < Fintype.card n := (Nat.zero_le k.val).trans_lt k.isLt
  have hlo (x : n → ℝ) : sigmaMin S ^ 2 * (x ⬝ᵥ x) ≤
      (Sᵀ *ᵥ x) ⬝ᵥ (Sᵀ *ᵥ x) := by
    simpa only [sigmaMin_transpose_eq S hn] using
      sq_sigmaMin_mul_dotProduct_le_mulVec_dotProduct Sᵀ x
  have hup (x : n → ℝ) : (Sᵀ *ᵥ x) ⬝ᵥ (Sᵀ *ᵥ x) ≤
      specNorm S ^ 2 * (x ⬝ᵥ x) := by
    simpa only [specNorm_transpose, dotProduct, pow_two] using sum_sq_mulVec_le_specNorm_sq Sᵀ x
  constructor
  · obtain ⟨V, hV, hAV⟩ := exists_submodule_eigenvalues₀_mul_le hA k
    have hdim := finrank_le_finrank_comap_endomorphism V Sᵀ.mulVecLin
    apply le_eigenvalues₀_of_forall_mem
      (Matrix.isHermitian_mul_mul_conjTranspose S hA) k (V.comap Sᵀ.mulVecLin) (by omega)
    intro x hx
    change Sᵀ *ᵥ x ∈ V at hx
    change _ ≤ quadForm (S * A * Sᵀ) x
    rw [quadForm_mul_mul_transpose]
    calc
      _ = hA.eigenvalues₀ k * (specNorm S ^ 2 * (x ⬝ᵥ x)) := by ring
      _ ≤ hA.eigenvalues₀ k * ((Sᵀ *ᵥ x) ⬝ᵥ (Sᵀ *ᵥ x)) :=
        mul_le_mul_of_nonpos_left (hup x) hk
      _ ≤ _ := hAV _ hx
  · obtain ⟨W, hW, hAW⟩ := exists_submodule_le_eigenvalues₀_mul hA k
    have hdim := finrank_le_finrank_comap_endomorphism W Sᵀ.mulVecLin
    apply eigenvalues₀_le_of_forall_mem
      (Matrix.isHermitian_mul_mul_conjTranspose S hA) k (W.comap Sᵀ.mulVecLin) (by omega)
    intro x hx
    change Sᵀ *ᵥ x ∈ W at hx
    change quadForm (S * A * Sᵀ) x ≤ _
    rw [quadForm_mul_mul_transpose]
    calc
      _ ≤ hA.eigenvalues₀ k * ((Sᵀ *ᵥ x) ⬝ᵥ (Sᵀ *ᵥ x)) := hAW _ hx
      _ ≤ hA.eigenvalues₀ k * (sigmaMin S ^ 2 * (x ⬝ᵥ x)) :=
        mul_le_mul_of_nonpos_left (hlo x) hk
      _ = _ := by ring

/-- Every congruence eigenvalue has a scaling factor in the closed interval
between squared extreme singular values, including singular transformations.
Horn--Johnson (2013), Theorem 4.5.9.
atlas: ostrowski-congruence-eigenvalues (partial) -/
theorem exists_eigenvalues₀_congruence_scale {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (S : Matrix n n ℝ) (k : Fin (Fintype.card n)) :
    ∃ θ : ℝ, sigmaMin S ^ 2 ≤ θ ∧ θ ≤ specNorm S ^ 2 ∧
      (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k = θ * hA.eigenvalues₀ k := by
  have hn : 0 < Fintype.card n := (Nat.zero_le k.val).trans_lt k.isLt
  let : Nonempty n := Fintype.card_pos_iff.mp hn
  have hscale : sigmaMin S ^ 2 ≤ specNorm S ^ 2 :=
    pow_le_pow_left₀ (sigmaMin_nonneg S) (sigmaMin_le_specNorm S) 2
  by_cases hz : hA.eigenvalues₀ k = 0
  · have hb := eigenvalues₀_congruence_bounds_of_nonneg hA S k (by rw [hz])
    refine ⟨sigmaMin S ^ 2, le_rfl, hscale, ?_⟩
    rw [hz] at hb ⊢
    simp only [mul_zero] at hb ⊢
    exact le_antisymm hb.2 hb.1
  · rcases lt_or_gt_of_ne hz with hneg | hpos
    · have hb := eigenvalues₀_congruence_bounds_of_nonpos hA S k hneg.le
      refine ⟨(Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k /
        hA.eigenvalues₀ k, ?_, ?_, ?_⟩
      · exact (le_div_iff_of_neg hneg).mpr hb.2
      · exact (div_le_iff_of_neg hneg).mpr hb.1
      · rw [div_mul_cancel₀ _ hz]
    · have hb := eigenvalues₀_congruence_bounds_of_nonneg hA S k hpos.le
      refine ⟨(Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k /
        hA.eigenvalues₀ k, ?_, ?_, ?_⟩
      · exact (le_div_iff₀ hpos).mpr hb.1
      · exact (div_le_iff₀ hpos).mpr hb.2
      · rw [div_mul_cancel₀ _ hz]

/-- An invertible real square matrix on a nonempty space has a positive
smallest singular value. Rank and singular-value support;
helper for `ostrowski-congruence-eigenvalues`. -/
theorem sigmaMin_pos_of_isUnit (S : Matrix n n ℝ) (hS : IsUnit S)
    (hn : 0 < Fintype.card n) : 0 < sigmaMin S := by
  have hr : (S.reindex (Fintype.equivFin n) (Fintype.equivFin n)).rank = Fintype.card n := by
    rw [Matrix.rank_reindex]
    exact Matrix.rank_of_isUnit S hS
  have hp := (sigmaMin_pos_iff_rank_eq_width
    (S.reindex (Fintype.equivFin n) (Fintype.equivFin n)) hn).mpr hr
  simpa only [sigmaMin_reindex] using hp

/-- Every congruence scaling factor can be chosen positive when the
transformation is invertible. Horn--Johnson (2013), Theorem 4.5.9.
atlas: ostrowski-congruence-eigenvalues (partial) -/
theorem exists_pos_eigenvalues₀_congruence_scale {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (S : Matrix n n ℝ) (hS : IsUnit S) (k : Fin (Fintype.card n)) :
    ∃ θ : ℝ, sigmaMin S ^ 2 ≤ θ ∧ θ ≤ specNorm S ^ 2 ∧ 0 < θ ∧
      (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k = θ * hA.eigenvalues₀ k := by
  obtain ⟨θ, hlo, hup, heq⟩ := exists_eigenvalues₀_congruence_scale hA S k
  have hmin := sigmaMin_pos_of_isUnit S hS ((Nat.zero_le k.val).trans_lt k.isLt)
  exact ⟨θ, hlo, hup, (sq_pos_of_pos hmin).trans_le hlo, heq⟩

/-- Congruence cannot increase the number of positive eigenvalues, even
for a singular transformation. Horn--Johnson (2013), Corollary 4.5.11.
atlas: ostrowski-congruence-eigenvalues (partial) -/
theorem card_eigenvalues₀_pos_congruence_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (S : Matrix n n ℝ) :
    (Finset.univ.filter fun k =>
      0 < (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k).card ≤
      (Finset.univ.filter fun k => 0 < hA.eigenvalues₀ k).card := by
  apply Finset.card_le_card
  intro k hk
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hpos := (Finset.mem_filter.mp hk).2
  by_contra h
  have hneg : hA.eigenvalues₀ k ≤ 0 := le_of_not_gt h
  have hb := (eigenvalues₀_congruence_bounds_of_nonpos hA S k hneg).2
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (sigmaMin S)) hneg
  exact (not_lt_of_ge (hb.trans hnonpos)) hpos

/-- Congruence cannot increase the number of negative eigenvalues, even
for a singular transformation. Horn--Johnson (2013), Corollary 4.5.11.
atlas: ostrowski-congruence-eigenvalues (partial) -/
theorem card_eigenvalues₀_neg_congruence_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (S : Matrix n n ℝ) :
    (Finset.univ.filter fun k =>
      (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k < 0).card ≤
      (Finset.univ.filter fun k => hA.eigenvalues₀ k < 0).card := by
  apply Finset.card_le_card
  intro k hk
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hneg := (Finset.mem_filter.mp hk).2
  by_contra h
  have hpos : 0 ≤ hA.eigenvalues₀ k := le_of_not_gt h
  have hb := (eigenvalues₀_congruence_bounds_of_nonneg hA S k hpos).1
  have hnonneg := mul_nonneg (sq_nonneg (sigmaMin S)) hpos
  exact (not_lt_of_ge (hnonneg.trans hb)) hneg

/-- The full Ostrowski contract gives scaling coefficients, signed sharp
bounds, positive coefficients for invertible transformations, and both
inertia-count contractions. The endpoints are the variational smallest
singular value and spectral norm, linked to the actual extreme singular list.
Horn--Johnson (2013), Theorem 4.5.9 and Corollary 4.5.11.
atlas: ostrowski-congruence-eigenvalues -/
theorem ostrowski_congruence_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (S : Matrix n n ℝ) :
    (∀ k, ∃ θ : ℝ, sigmaMin S ^ 2 ≤ θ ∧ θ ≤ specNorm S ^ 2 ∧
      (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k = θ * hA.eigenvalues₀ k) ∧
    (IsUnit S → ∀ k, ∃ θ : ℝ, sigmaMin S ^ 2 ≤ θ ∧ θ ≤ specNorm S ^ 2 ∧ 0 < θ ∧
      (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k = θ * hA.eigenvalues₀ k) ∧
    (∀ k, 0 ≤ hA.eigenvalues₀ k → sigmaMin S ^ 2 * hA.eigenvalues₀ k ≤
      (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k ∧
      (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k ≤
        specNorm S ^ 2 * hA.eigenvalues₀ k) ∧
    (∀ k, hA.eigenvalues₀ k ≤ 0 → specNorm S ^ 2 * hA.eigenvalues₀ k ≤
      (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k ∧
      (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k ≤
        sigmaMin S ^ 2 * hA.eigenvalues₀ k) ∧
    (Finset.univ.filter fun k =>
      0 < (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k).card ≤
      (Finset.univ.filter fun k => 0 < hA.eigenvalues₀ k).card ∧
    (Finset.univ.filter fun k =>
      (Matrix.isHermitian_mul_mul_conjTranspose S hA).eigenvalues₀ k < 0).card ≤
      (Finset.univ.filter fun k => hA.eigenvalues₀ k < 0).card :=
  ⟨exists_eigenvalues₀_congruence_scale hA S,
    fun hS => exists_pos_eigenvalues₀_congruence_scale hA S hS,
    eigenvalues₀_congruence_bounds_of_nonneg hA S,
    eigenvalues₀_congruence_bounds_of_nonpos hA S,
    card_eigenvalues₀_pos_congruence_le hA S, card_eigenvalues₀_neg_congruence_le hA S⟩

end NLAlib
