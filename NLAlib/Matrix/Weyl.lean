import NLAlib.Matrix.CourantFischer
import NLAlib.Matrix.EckartYoung
import NLAlib.Matrix.VonNeumann

/-!
# Weyl inequalities for singular values and the spectral Eckart–Young theorem

* `singularValues_add_add_le`: Weyl's inequality `σ_{i+j}(A + B) ≤ σ_i(A) + σ_j(B)`;
* `singularValues_add_le_add_specNorm`, `singularValues_le_singularValues_add_add_specNorm`,
  `abs_singularValues_add_sub_le_specNorm`: perturbation `|σ_k(A + E) − σ_k(A)| ≤ ‖E‖₂`;
* `singularValues_mul_le_specNorm_mul`, `singularValues_mul_le_mul_specNorm`,
  `singularValues_residual_le`: `σ_k(BA) ≤ ‖B‖₂ σ_k(A)`, `σ_k(AC) ≤ σ_k(A) ‖C‖₂`,
  `σ_k((I − QQᵀ)A) ≤ σ_k(A)`;
* `singularValues_le_specNorm_sub_of_rank_le`, `isLeast_specNorm_sub_of_rank_le`: the spectral
  Eckart–Young theorem `min_{rank B ≤ k} ‖A − B‖₂ = σ_k(A)`, attained by `truncatedSVD A k`;
* `sum_sq_singularValues_add_sub_le_frobSq`: Mirsky's inequality
  `∑ₖ (σ_k(A + E) − σ_k(A))² ≤ ‖E‖_F²`, from the von Neumann trace inequality.

All singular values are zero-indexed (`σ 0 = ‖A‖₂`) and padded with zeros, so no index side
conditions are needed.

Source: Horn–Johnson 2013, §7.3 (Weyl inequalities for singular values) and §7.4.9
(Eckart–Young–Mirsky); Mirsky 1960; Bhatia 1997, §III.2 and §IV.3. Theorem labels marked
"verify" were not checked against the printed edition. Audit G0 B2, B3, B4, B5, B6.
Atlas: `weyl-mirsky`, `eckart-young`.
Deviation from the audit's file plan: the spectral Eckart–Young lower bound (B5) lives here
rather than in `EckartYoung`, because it needs Weyl's inequality and this file imports
`EckartYoung` (for `truncatedSVD`).
-/

noncomputable section

open scoped Matrix
open Module

namespace NLAlib

variable {m n p : ℕ}

private theorem sqrt_le_mul_sqrt_of_le {u : Fin m → ℝ} {x : Fin n → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : u ⬝ᵥ u ≤ c ^ 2 * (x ⬝ᵥ x)) : Real.sqrt (u ⬝ᵥ u) ≤ c * Real.sqrt (x ⬝ᵥ x) := by
  calc Real.sqrt (u ⬝ᵥ u) ≤ Real.sqrt (c ^ 2 * (x ⬝ᵥ x)) := Real.sqrt_le_sqrt h
    _ = c * Real.sqrt (x ⬝ᵥ x) := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

private theorem le_of_sqrt_le_mul_sqrt {u : Fin m → ℝ} {x : Fin n → ℝ} {c : ℝ}
    (h : Real.sqrt (u ⬝ᵥ u) ≤ c * Real.sqrt (x ⬝ᵥ x)) : u ⬝ᵥ u ≤ c ^ 2 * (x ⬝ᵥ x) := by
  have h0 : 0 ≤ Real.sqrt (u ⬝ᵥ u) := Real.sqrt_nonneg _
  have h2 := pow_le_pow_left₀ h0 h 2
  rwa [Real.sq_sqrt (dotProduct_self_nonneg u), mul_pow,
    Real.sq_sqrt (dotProduct_self_nonneg x)] at h2

/-- **Weyl's inequality for singular values.** `σ_{i+j}(A + B) ≤ σ_i(A) + σ_j(B)` for real
`m × n` matrices (zero-indexed). Horn–Johnson 2013, §7.3 (Cor 7.3.5, label to verify); Bhatia
1997, Thm III.2.1 (Hermitian eigenvalue form). Audit G0 B2; atlas `weyl-mirsky`.
atlas: weyl-mirsky -/
theorem singularValues_add_add_le (A B : Matrix (Fin m) (Fin n) ℝ) (i j : ℕ) :
    singularValues (A + B) (i + j) ≤ singularValues A i + singularValues B j := by
  obtain ⟨W₁, h₁, hA⟩ := exists_submodule_mulVec_dotProduct_le_sq_singularValues_mul A i
  obtain ⟨W₂, h₂, hB⟩ := exists_submodule_mulVec_dotProduct_le_sq_singularValues_mul B j
  have hσA := singularValues_nonneg A i
  have hσB := singularValues_nonneg B j
  have hW := card_le_finrank_inf_add (n := Fin n) (by simpa using h₁) (by simpa using h₂)
  rw [Fintype.card_fin] at hW
  refine singularValues_le_of_forall_mem (A + B) (i + j) (W₁ ⊓ W₂) hW (add_nonneg hσA hσB)
    fun x hx => le_of_sqrt_le_mul_sqrt ?_
  have ha := sqrt_le_mul_sqrt_of_le hσA (hA x hx.1)
  have hb := sqrt_le_mul_sqrt_of_le hσB (hB x hx.2)
  calc Real.sqrt ((A + B) *ᵥ x ⬝ᵥ (A + B) *ᵥ x)
      ≤ Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) + Real.sqrt ((B *ᵥ x) ⬝ᵥ (B *ᵥ x)) := by
        rw [Matrix.add_mulVec]; exact sqrt_dotProduct_add_le _ _
    _ ≤ (singularValues A i + singularValues B j) * Real.sqrt (x ⬝ᵥ x) := by linarith

/-- **Weyl perturbation bound, upper side.** `σ_k(A + E) ≤ σ_k(A) + ‖E‖₂`. Horn–Johnson 2013,
§7.3 (Cor 7.3.5, label to verify). Audit G0 B3; atlas `weyl-mirsky`. -/
theorem singularValues_add_le_add_specNorm (A E : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    singularValues (A + E) k ≤ singularValues A k + specNorm E := by
  have h := singularValues_add_add_le A E k 0
  rwa [Nat.add_zero, singularValues_zero_eq_specNorm] at h

/-- **Weyl perturbation bound, lower side.** `σ_k(A) ≤ σ_k(A + E) + ‖E‖₂`. Horn–Johnson 2013,
§7.3 (Cor 7.3.5, label to verify). Audit G0 B3; atlas `weyl-mirsky`. -/
theorem singularValues_le_singularValues_add_add_specNorm (A E : Matrix (Fin m) (Fin n) ℝ)
    (k : ℕ) : singularValues A k ≤ singularValues (A + E) k + specNorm E := by
  have h := singularValues_add_le_add_specNorm (A + E) (-E) k
  rwa [add_neg_cancel_right, specNorm_neg] at h

/-- **Weyl perturbation bound.** `|σ_k(A + E) − σ_k(A)| ≤ ‖E‖₂` for every `k`. Horn–Johnson
2013, §7.3 (Cor 7.3.5, label to verify); Bhatia 1997, §III.2. Audit G0 B3; atlas `weyl-mirsky`.
atlas: weyl-mirsky -/
theorem abs_singularValues_add_sub_le_specNorm (A E : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    |singularValues (A + E) k - singularValues A k| ≤ specNorm E := by
  have h1 := singularValues_add_le_add_specNorm A E k
  have h2 := singularValues_le_singularValues_add_add_specNorm A E k
  rw [abs_le]; constructor <;> linarith

/-- **Left multiplication.** `σ_k(BA) ≤ ‖B‖₂ σ_k(A)`. Horn–Johnson 2013, §7.3; Bhatia 1997,
§III.6 (the special case `i = 0` of `σ_{i+j}(BA) ≤ σ_i(B) σ_j(A)`). Audit G0 B6;
atlas `weyl-mirsky` (new corollary `singularValues_mul_le`).
atlas: weyl-mirsky -/
theorem singularValues_mul_le_specNorm_mul (B : Matrix (Fin p) (Fin m) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    singularValues (B * A) k ≤ specNorm B * singularValues A k := by
  obtain ⟨W, hW, hA⟩ := exists_submodule_mulVec_dotProduct_le_sq_singularValues_mul A k
  have hσ := singularValues_nonneg A k
  have hB := specNorm_nonneg B
  refine singularValues_le_of_forall_mem (B * A) k W hW (mul_nonneg hB hσ)
    fun x hx => le_of_sqrt_le_mul_sqrt ?_
  have ha := sqrt_le_mul_sqrt_of_le hσ (hA x hx)
  calc Real.sqrt ((B * A) *ᵥ x ⬝ᵥ (B * A) *ᵥ x)
      ≤ specNorm B * Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by
        rw [← Matrix.mulVec_mulVec]; exact sqrt_mulVec_dotProduct_le_specNorm_mul B _
    _ ≤ specNorm B * (singularValues A k * Real.sqrt (x ⬝ᵥ x)) :=
        mul_le_mul_of_nonneg_left ha hB
    _ = specNorm B * singularValues A k * Real.sqrt (x ⬝ᵥ x) := by ring

/-- **Right multiplication.** `σ_k(AC) ≤ σ_k(A) ‖C‖₂`. Horn–Johnson 2013, §7.3 (transpose of
`singularValues_mul_le_specNorm_mul`). Audit G0 B6; atlas `weyl-mirsky`. -/
theorem singularValues_mul_le_mul_specNorm (A : Matrix (Fin m) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    singularValues (A * C) k ≤ singularValues A k * specNorm C := by
  have h := singularValues_mul_le_specNorm_mul Cᵀ Aᵀ k
  rw [← Matrix.transpose_mul, singularValues_transpose, singularValues_transpose,
    specNorm_transpose] at h
  linarith

/-- **Projection does not increase singular values.** For `Q` with orthonormal columns,
`σ_k((I − QQᵀ)A) ≤ σ_k(A)`. HMT 2011, §8.4 (used in Prop 8.6 and Thm 9.2). Audit G0 B6;
atlas `weyl-mirsky`, `projection-facts`.
atlas: projection-facts -/
theorem singularValues_residual_le {q : Type*} [Fintype q] [DecidableEq q]
    {Q : Matrix (Fin m) q ℝ} (hQ : HasOrthonormalCols Q) (A : Matrix (Fin m) (Fin n) ℝ)
    (k : ℕ) : singularValues (residual Q A) k ≤ singularValues A k := by
  have hP : specNorm (1 - Q * Qᵀ : Matrix (Fin m) (Fin m) ℝ) ≤ 1 := by
    have h := specNorm_sub_mul_transpose_mul_le hQ (1 : Matrix (Fin m) (Fin m) ℝ)
    rw [Matrix.mul_one] at h
    exact h.trans specNorm_one_le
  rw [residual_eq_one_sub_mul]
  calc singularValues ((1 - Q * Qᵀ) * A) k ≤ specNorm (1 - Q * Qᵀ) * singularValues A k :=
        singularValues_mul_le_specNorm_mul _ A k
    _ ≤ 1 * singularValues A k :=
        mul_le_mul_of_nonneg_right hP (singularValues_nonneg A k)
    _ = singularValues A k := one_mul _

/-- **Spectral Eckart–Young, lower bound.** Every competitor of rank at most `k` has spectral
error at least `σ_k(A)` (zero-indexed): `σ_k(A) ≤ ‖A − B‖₂`. Horn–Johnson 2013, Thm 7.4.9.1
(spectral case); HMT 2011, eq. (2.3). Audit G0 B5; atlas `eckart-young`.
atlas: eckart-young -/
theorem singularValues_le_specNorm_sub_of_rank_le (A B : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (hB : B.rank ≤ k) : singularValues A k ≤ specNorm (A - B) := by
  have h := singularValues_add_add_le (A - B) B 0 k
  rwa [sub_add_cancel, Nat.zero_add, singularValues_zero_eq_specNorm,
    singularValues_eq_zero_of_rank_le B hB, add_zero] at h

/-- **Spectral Eckart–Young theorem.** `σ_k(A)` is the least spectral error of a rank-`≤ k`
approximation, attained by `truncatedSVD A k`. Horn–Johnson 2013, Thm 7.4.9.1; HMT 2011,
eq. (2.3). Audit G0 B5 + C3; atlas `eckart-young`.
atlas: eckart-young -/
theorem isLeast_specNorm_sub_of_rank_le (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    IsLeast {v : ℝ | ∃ B : Matrix (Fin m) (Fin n) ℝ, B.rank ≤ k ∧ v = specNorm (A - B)}
      (singularValues A k) := by
  refine ⟨⟨truncatedSVD A k, (isBestRankApprox_truncatedSVD A k).1,
    (specNorm_sub_truncatedSVD_eq A k).symm⟩, ?_⟩
  rintro v ⟨B, hB, rfl⟩
  exact singularValues_le_specNorm_sub_of_rank_le A B hB

/-- **Mirsky's inequality** (Frobenius half of Weyl–Mirsky):
`∑_{k < min m n} (σ_k(A + E) − σ_k(A))² ≤ ‖E‖_F²`. Proof: expand
`‖E‖_F² = ‖A + E‖_F² − 2⟨A + E, A⟩_F + ‖A‖_F²` and bound the inner product by the von Neumann
trace inequality. Mirsky 1960 (Q. J. Math. 11); Horn–Johnson 2013, §7.4.9 (label to verify);
Bhatia 1997, §IV.3 (unitarily invariant form). Audit G0 B4;
atlas `weyl-mirsky`.
atlas: weyl-mirsky -/
theorem sum_sq_singularValues_add_sub_le_frobSq (A E : Matrix (Fin m) (Fin n) ℝ) :
    ∑ k ∈ Finset.range (min m n), (singularValues (A + E) k - singularValues A k) ^ 2 ≤
      frobSq E := by
  have hvN := frobInner_le_sum_singularValues_mul (A + E) A
  have hF : frobSq E = frobSq (A + E) - 2 * frobInner (A + E) A + frobSq A := by
    rw [← frobSq_sub]
    congr 1
    abel
  have hexp : ∑ k ∈ Finset.range (min m n),
      (singularValues (A + E) k - singularValues A k) ^ 2 =
      ∑ k ∈ Finset.range (min m n), singularValues (A + E) k ^ 2 -
        2 * ∑ k ∈ Finset.range (min m n), singularValues (A + E) k * singularValues A k +
        ∑ k ∈ Finset.range (min m n), singularValues A k ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hexp, hF, frobSq_eq_sum_sq_singularValues, frobSq_eq_sum_sq_singularValues]
  linarith

end NLAlib
