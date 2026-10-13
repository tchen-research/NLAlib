import NLAlib.Matrix.Spectral.CourantFischer
import NLAlib.Matrix.Spectral.SpectralBounds
import NLAlib.Matrix.Inequalities.VonNeumann
import NLAlib.Matrix.Norms.SchattenTrace
/-!
# Weyl inequalities for singular values and the spectral Eckart–Young theorem

* `singularValues_add_add_le`: Weyl's inequality `σ_{i+j}(A + B) ≤ σ_i(A) + σ_j(B)`;
* `singularValues_add_le_add_specNorm`, `singularValues_le_singularValues_add_add_specNorm`,
  `abs_singularValues_add_sub_le_specNorm`: perturbation `|σ_k(A + E) − σ_k(A)| ≤ ‖E‖₂`;
* `singularValues_mul_le_specNorm_mul`, `singularValues_mul_le_mul_specNorm`,
  `singularValues_residual_le`: `σ_k(BA) ≤ ‖B‖₂ σ_k(A)`, `σ_k(AC) ≤ σ_k(A) ‖C‖₂`,
  `σ_k((I − QQᴴ)A) ≤ σ_k(A)`;
* `singularValues_le_specNorm_sub_of_rank_le`, `isLeast_specNorm_sub_of_rank_le`: the spectral
  Eckart–Young theorem `min_{rank B ≤ k} ‖A − B‖₂ = σ_k(A)`, attained by `truncatedSVD A k`;
* `sum_sq_singularValues_add_sub_le_frobSq`: Mirsky's inequality
  `∑ₖ (σ_k(A + E) − σ_k(A))² ≤ ‖E‖_F²`, from the von Neumann trace inequality.

All singular values are zero-indexed (`σ 0 = ‖A‖₂`) and padded with zeros, so no index side
conditions are needed. Everything is stated on arbitrary finite index types, and everything
except Mirsky's inequality over `[RCLike 𝕜]`; Mirsky's inequality is real (it rests on the real
von Neumann trace inequality).

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

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] in
/-- `re (uᴴu) = ‖u‖₂²` (Euclidean norm of `WithLp.toLp 2 u`). -/
private theorem re_star_dotProduct_self_eq_norm_sq (u : m → 𝕜) :
    RCLike.re (star u ⬝ᵥ u) = ‖WithLp.toLp 2 u‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, Pi.star_apply, map_sum, RCLike.star_def, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.ofReal_re]

omit [DecidableEq m] [DecidableEq n] in
private theorem norm_le_mul_norm_of_le {u : m → 𝕜} {x : n → 𝕜} {c : ℝ} (hc : 0 ≤ c)
    (h : RCLike.re (star u ⬝ᵥ u) ≤ c ^ 2 * RCLike.re (star x ⬝ᵥ x)) :
    ‖WithLp.toLp 2 u‖ ≤ c * ‖WithLp.toLp 2 x‖ := by
  rw [re_star_dotProduct_self_eq_norm_sq, re_star_dotProduct_self_eq_norm_sq, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)) two_ne_zero).1 h

omit [DecidableEq m] [DecidableEq n] in
private theorem le_of_norm_le_mul_norm {u : m → 𝕜} {x : n → 𝕜} {c : ℝ}
    (h : ‖WithLp.toLp 2 u‖ ≤ c * ‖WithLp.toLp 2 x‖) :
    RCLike.re (star u ⬝ᵥ u) ≤ c ^ 2 * RCLike.re (star x ⬝ᵥ x) := by
  rw [re_star_dotProduct_self_eq_norm_sq, re_star_dotProduct_self_eq_norm_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

omit [DecidableEq m] in
/-- `‖Bx‖₂ ≤ ‖B‖₂ ‖x‖₂` for the Euclidean norms of coordinate vectors. -/
private theorem norm_mulVec_le_specNorm_mul (B : Matrix m n 𝕜) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (B *ᵥ x)‖ ≤ specNorm B * ‖WithLp.toLp 2 x‖ := by
  have h := sum_norm_sq_mulVec_le_specNorm_sq B x
  refine norm_le_mul_norm_of_le (specNorm_nonneg B) ?_
  rw [re_star_dotProduct_self_eq_norm_sq, re_star_dotProduct_self_eq_norm_sq,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simpa using h

omit [DecidableEq m] in
/-- **Weyl's inequality for singular values.** `σ_{i+j}(A + B) ≤ σ_i(A) + σ_j(B)` for
`m × n` matrices over `𝕜` (zero-indexed). Horn–Johnson 2013, §7.3 (Cor 7.3.5, label to verify);
Bhatia 1997, Thm III.2.1 (Hermitian eigenvalue form). Audit G0 B2; atlas `weyl-mirsky`.
atlas: weyl-mirsky -/
theorem singularValues_add_add_le (A B : Matrix m n 𝕜) (i j : ℕ) :
    singularValues (A + B) (i + j) ≤ singularValues A i + singularValues B j := by
  obtain ⟨W₁, h₁, hA⟩ := exists_submodule_mulVec_dotProduct_le_sq_singularValues_mul A i
  obtain ⟨W₂, h₂, hB⟩ := exists_submodule_mulVec_dotProduct_le_sq_singularValues_mul B j
  have hσA := singularValues_nonneg A i
  have hσB := singularValues_nonneg B j
  have hW := card_le_finrank_inf_add h₁ h₂
  refine singularValues_le_of_forall_mem (A + B) (i + j) (W₁ ⊓ W₂) hW (add_nonneg hσA hσB)
    fun x hx => le_of_norm_le_mul_norm ?_
  have ha := norm_le_mul_norm_of_le hσA (hA x hx.1)
  have hb := norm_le_mul_norm_of_le hσB (hB x hx.2)
  calc ‖WithLp.toLp 2 ((A + B) *ᵥ x)‖
      ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖ + ‖WithLp.toLp 2 (B *ᵥ x)‖ := by
        rw [Matrix.add_mulVec, WithLp.toLp_add]; exact norm_add_le _ _
    _ ≤ (singularValues A i + singularValues B j) * ‖WithLp.toLp 2 x‖ := by linarith

/-- **Weyl perturbation bound, upper side.** `σ_k(A + E) ≤ σ_k(A) + ‖E‖₂`. Horn–Johnson 2013,
§7.3 (Cor 7.3.5, label to verify). Audit G0 B3; atlas `weyl-mirsky`. -/
theorem singularValues_add_le_add_specNorm (A E : Matrix m n 𝕜) (k : ℕ) :
    singularValues (A + E) k ≤ singularValues A k + specNorm E := by
  have h := singularValues_add_add_le A E k 0
  rwa [Nat.add_zero, singularValues_zero_eq_specNorm] at h

/-- **Weyl perturbation bound, lower side.** `σ_k(A) ≤ σ_k(A + E) + ‖E‖₂`. Horn–Johnson 2013,
§7.3 (Cor 7.3.5, label to verify). Audit G0 B3; atlas `weyl-mirsky`. -/
theorem singularValues_le_singularValues_add_add_specNorm (A E : Matrix m n 𝕜)
    (k : ℕ) : singularValues A k ≤ singularValues (A + E) k + specNorm E := by
  have h := singularValues_add_le_add_specNorm (A + E) (-E) k
  rwa [add_neg_cancel_right, specNorm_neg] at h

/-- **Weyl perturbation bound.** `|σ_k(A + E) − σ_k(A)| ≤ ‖E‖₂` for every `k`. Horn–Johnson
2013, §7.3 (Cor 7.3.5, label to verify); Bhatia 1997, §III.2. Audit G0 B3; atlas `weyl-mirsky`.
atlas: weyl-mirsky -/
theorem abs_singularValues_add_sub_le_specNorm (A E : Matrix m n 𝕜) (k : ℕ) :
    |singularValues (A + E) k - singularValues A k| ≤ specNorm E := by
  have h1 := singularValues_add_le_add_specNorm A E k
  have h2 := singularValues_le_singularValues_add_add_specNorm A E k
  rw [abs_le]; constructor <;> linarith

omit [DecidableEq p] in
/-- **Left multiplication.** `σ_k(BA) ≤ ‖B‖₂ σ_k(A)`. Horn–Johnson 2013, §7.3; Bhatia 1997,
§III.6 (the special case `i = 0` of `σ_{i+j}(BA) ≤ σ_i(B) σ_j(A)`). Audit G0 B6;
atlas `weyl-mirsky` (new corollary `singularValues_mul_le`).
atlas: weyl-mirsky -/
theorem singularValues_mul_le_specNorm_mul (B : Matrix p m 𝕜) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (B * A) k ≤ specNorm B * singularValues A k := by
  obtain ⟨W, hW, hA⟩ := exists_submodule_mulVec_dotProduct_le_sq_singularValues_mul A k
  have hσ := singularValues_nonneg A k
  have hB := specNorm_nonneg B
  refine singularValues_le_of_forall_mem (B * A) k W hW (mul_nonneg hB hσ)
    fun x hx => le_of_norm_le_mul_norm ?_
  have ha := norm_le_mul_norm_of_le hσ (hA x hx)
  calc ‖WithLp.toLp 2 ((B * A) *ᵥ x)‖
      ≤ specNorm B * ‖WithLp.toLp 2 (A *ᵥ x)‖ := by
        rw [← Matrix.mulVec_mulVec]; exact norm_mulVec_le_specNorm_mul B _
    _ ≤ specNorm B * (singularValues A k * ‖WithLp.toLp 2 x‖) :=
        mul_le_mul_of_nonneg_left ha hB
    _ = specNorm B * singularValues A k * ‖WithLp.toLp 2 x‖ := by ring

omit [DecidableEq m] in
/-- **Right multiplication.** `σ_k(AC) ≤ σ_k(A) ‖C‖₂`. Horn–Johnson 2013, §7.3. Proof: the
preimage under `C` of the min-max subspace of `A` has codimension at most `k`.
Audit G0 B6; atlas `weyl-mirsky`. -/
theorem singularValues_mul_le_mul_specNorm (A : Matrix m n 𝕜) (C : Matrix n p 𝕜) (k : ℕ) :
    singularValues (A * C) k ≤ singularValues A k * specNorm C := by
  obtain ⟨W, hW, hA⟩ := exists_submodule_mulVec_dotProduct_le_sq_singularValues_mul A k
  have hσ := singularValues_nonneg A k
  have hC := specNorm_nonneg C
  -- the preimage `C⁻¹ W` has codimension at most `k`
  have hdim : Fintype.card p ≤ Module.finrank 𝕜 (W.comap C.mulVecLin) + k := by
    set g := W.mkQ ∘ₗ C.mulVecLin
    have hker : LinearMap.ker g = W.comap C.mulVecLin := by
      ext x; simp [g, Submodule.mem_comap]
    have h1 := LinearMap.finrank_range_add_finrank_ker g
    have h2 : Module.finrank 𝕜 (LinearMap.range g) ≤ Module.finrank 𝕜 ((n → 𝕜) ⧸ W) :=
      Submodule.finrank_le _
    have h3 := Submodule.finrank_quotient_add_finrank W
    rw [Module.finrank_fintype_fun_eq_card] at h1 h3
    rw [hker] at h1
    omega
  refine singularValues_le_of_forall_mem (A * C) k _ hdim (mul_nonneg hσ hC)
    fun x hx => le_of_norm_le_mul_norm ?_
  have ha := norm_le_mul_norm_of_le hσ (hA (C *ᵥ x) hx)
  calc ‖WithLp.toLp 2 ((A * C) *ᵥ x)‖
      ≤ singularValues A k * ‖WithLp.toLp 2 (C *ᵥ x)‖ := by
        rw [← Matrix.mulVec_mulVec]; exact ha
    _ ≤ singularValues A k * (specNorm C * ‖WithLp.toLp 2 x‖) :=
        mul_le_mul_of_nonneg_left (norm_mulVec_le_specNorm_mul C x) hσ
    _ = singularValues A k * specNorm C * ‖WithLp.toLp 2 x‖ := by ring

omit [DecidableEq m] in
/-- **Projection does not increase singular values.** For `Q` with orthonormal columns,
`σ_k((I − QQᴴ)A) ≤ σ_k(A)`. HMT 2011, §8.4 (used in Prop 8.6 and Thm 9.2). Audit G0 B6;
atlas `weyl-mirsky`, `projection-facts`.
atlas: projection-facts -/
theorem singularValues_residual_le {q : Type*} [Fintype q] [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜)
    (k : ℕ) : singularValues (projResidual Q A) k ≤ singularValues A k := by
  classical
  have hP : specNorm (1 - Q * Qᴴ : Matrix m m 𝕜) ≤ 1 := by
    have h := specNorm_sub_mul_conjTranspose_mul_le hQ (1 : Matrix m m 𝕜)
    rw [Matrix.mul_one] at h
    exact h.trans specNorm_one_le
  rw [residual_eq_one_sub_mul]
  calc singularValues ((1 - Q * Qᴴ) * A) k ≤ specNorm (1 - Q * Qᴴ) * singularValues A k :=
        singularValues_mul_le_specNorm_mul _ A k
    _ ≤ 1 * singularValues A k :=
        mul_le_mul_of_nonneg_right hP (singularValues_nonneg A k)
    _ = singularValues A k := one_mul _

/-- **Spectral Eckart–Young, lower bound.** Every competitor of rank at most `k` has spectral
error at least `σ_k(A)` (zero-indexed): `σ_k(A) ≤ ‖A − B‖₂`. Horn–Johnson 2013, Thm 7.4.9.1
(spectral case); HMT 2011, eq. (2.3). Audit G0 B5; atlas `eckart-young`.
atlas: eckart-young -/
theorem singularValues_le_specNorm_sub_of_rank_le (A B : Matrix m n 𝕜) {k : ℕ}
    (hB : B.rank ≤ k) : singularValues A k ≤ specNorm (A - B) := by
  have h := singularValues_add_add_le (A - B) B 0 k
  rwa [sub_add_cancel, Nat.zero_add, singularValues_zero_eq_specNorm,
    singularValues_eq_zero_of_rank_le B hB, add_zero] at h

/-- **Spectral Eckart–Young theorem.** `σ_k(A)` is the least spectral error of a rank-`≤ k`
approximation, attained by `truncatedSVD A k`. Horn–Johnson 2013, Thm 7.4.9.1; HMT 2011,
eq. (2.3). Audit G0 B5 + C3; atlas `eckart-young`.
atlas: eckart-young -/
theorem isLeast_specNorm_sub_of_rank_le (A : Matrix m n 𝕜) (k : ℕ) :
    IsLeast {v : ℝ | ∃ B : Matrix m n 𝕜, B.rank ≤ k ∧ v = specNorm (A - B)}
      (singularValues A k) := by
  refine ⟨⟨truncatedSVD A k, (isBestRankApprox_truncatedSVD A k).1,
    (specNorm_sub_truncatedSVD_eq A k).symm⟩, ?_⟩
  rintro v ⟨B, hB, rfl⟩
  exact singularValues_le_specNorm_sub_of_rank_le A B hB

/-- **Mirsky's inequality** (Frobenius half of Weyl–Mirsky):
`∑_{k < min m n} (σ_k(A + E) − σ_k(A))² ≤ ‖E‖_F²`, on arbitrary finite index types. Proof:
expand `‖E‖_F² = ‖A + E‖_F² − 2⟨A + E, A⟩_F + ‖A‖_F²` and bound the inner product by the von
Neumann trace inequality (`abs_frobInner_le_sum_singularValues_mul`). Mirsky 1960 (Q. J. Math.
11); Horn–Johnson 2013, §7.4.9 (label to verify); Bhatia 1997, §IV.3 (unitarily invariant
form). Audit G0 B4; atlas `weyl-mirsky`. Real only: the von Neumann trace inequality in the
library is real.
atlas: weyl-mirsky -/
theorem sum_sq_singularValues_add_sub_le_frobSq (A E : Matrix m n ℝ) :
    ∑ k ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        (singularValues (A + E) k - singularValues A k) ^ 2 ≤ frobSq E := by
  have hvN := (le_abs_self _).trans (abs_frobInner_le_sum_singularValues_mul (A + E) A)
  have hF : frobSq E = frobSq (A + E) - 2 * frobInner (A + E) A + frobSq A := by
    rw [← frobSq_sub]
    congr 1
    abel
  set N := min (Fintype.card m) (Fintype.card n)
  have hexp : ∑ k ∈ Finset.range N,
      (singularValues (A + E) k - singularValues A k) ^ 2 =
      ∑ k ∈ Finset.range N, singularValues (A + E) k ^ 2 -
        2 * ∑ k ∈ Finset.range N, singularValues (A + E) k * singularValues A k +
        ∑ k ∈ Finset.range N, singularValues A k ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hexp, hF, frobSq_eq_sum_sq_singularValues, frobSq_eq_sum_sq_singularValues]
  linarith

end NLAlib
