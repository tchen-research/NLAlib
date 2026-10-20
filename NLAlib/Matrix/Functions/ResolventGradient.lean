import NLAlib.Matrix.Norms.MatrixVarianceProxy
import NLAlib.Matrix.Norms.BilinearProbes
import NLAlib.Matrix.Functions.HermitianResolventLipschitz
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.SimpRw

/-!
# Actual Hermitian resolvent positive gradients

Constructed bilinear norm-attaining probes and the ordered second
resolvent identity give the genuine squared positive-gradient bound by
the computed variance proxy. Source: Brailovskaya--van Handel,
arXiv:2201.05142v3, Lemma5.7. This is a prerequisite for the retained
independent-sum-spectrum-universality card.
-/

noncomputable section
set_option autoImplicit false
open Matrix Finset
open scoped Matrix
namespace NLAlib
variable {n ι : Type*} [Fintype n] [DecidableEq n]

private theorem sum_norm_sq_mulVec_le_gram_mul (D : ι → Matrix n n ℂ)
    (s : Finset ι) (u : EuclideanSpace ℂ n) :
    ∑ i ∈ s, ‖WithLp.toLp 2 (D i *ᵥ u.ofLp)‖ ^ 2 ≤
      specNorm (∑ i ∈ s, (D i)ᴴ * D i) * ‖u‖ ^ 2 := by
  rw [sum_norm_sq_mulVec_eq_re_quadForm_sum_gram]
  exact (Complex.re_le_norm _).trans (by
    simpa only [WithLp.toLp_ofLp] using
      norm_quadForm_le_specNorm (∑ i ∈ s, (D i)ᴴ * D i) u.ofLp)

omit [DecidableEq n] in
private theorem bilinear_move_left (B : Matrix n n ℂ) (v : n → ℂ) (x : n → ℂ) :
    star v ⬝ᵥ (B *ᵥ x) = star (Bᴴ *ᵥ v) ⬝ᵥ x := by
  simp only [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

open scoped Matrix.Norms.L2Operator in
private theorem sum_posPart_sq_le_of_resolvent_expansion [Fintype ι]
    (S : Matrix n n ℂ) (T D : ι → Matrix n n ℂ) {c R : ℝ}
    (hc : 0 < c) (hR : 0 ≤ R) (hS : specNorm S ≤ c)
    (hT : ∀ i, specNorm (T i) ≤ c) (hD : ∀ i, specNorm (D i) ≤ 2 * R)
    (hexp : ∀ i, S - T i = S * D i * S - S * D i * T i * D i * S) :
    ∑ i, max (specNorm S - specNorm (T i)) 0 ^ 2 ≤
      2 * c ^ 4 * bilinearSquareMass D Finset.univ +
        8 * R ^ 2 * c ^ 6 * specNorm (∑ i, (D i)ᴴ * D i) := by
  obtain ⟨v, w, hv, hw, hprobe⟩ := exists_unitBall_bilinear_eq_specNorm S
  let p : EuclideanSpace ℂ n := WithLp.toLp 2 (Sᴴ *ᵥ v.ofLp)
  let q : EuclideanSpace ℂ n := WithLp.toLp 2 (S *ᵥ w.ofLp)
  let a : ι → ℝ := fun i => ‖star p.ofLp ⬝ᵥ (D i *ᵥ q.ofLp)‖
  let b : ι → ℝ := fun i => ‖star v.ofLp ⬝ᵥ ((S * D i * T i * D i * S) *ᵥ w.ofLp)‖
  have hp : ‖p‖ ≤ c := by
    exact ((Sᴴ).l2_opNorm_mulVec v).trans
      ((mul_le_mul_of_nonneg_left hv (specNorm_nonneg _)).trans
        (by simpa only [mul_one, specNorm_conjTranspose] using hS))
  have hq : ‖q‖ ≤ c := by
    exact (S.l2_opNorm_mulVec w).trans
      ((mul_le_mul_of_nonneg_left hw (specNorm_nonneg _)).trans
        (by simpa only [mul_one] using hS))
  have hleading (i : ι) :
      star v.ofLp ⬝ᵥ ((S * D i * S) *ᵥ w.ofLp) =
        star p.ofLp ⬝ᵥ (D i *ᵥ q.ofLp) := by
    dsimp [p, q]
    simp only [← Matrix.mulVec_mulVec]
    rw [bilinear_move_left S]
  have hdiff (i : ι) : max (specNorm S - specNorm (T i)) 0 ≤ a i + b i := by
    apply max_le _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
    have hsmall := norm_star_dotProduct_mulVec_le_specNorm (T i) v w hv hw
    have hrev := norm_sub_norm_le
      (star v.ofLp ⬝ᵥ (S *ᵥ w.ofLp)) (star v.ofLp ⬝ᵥ (T i *ᵥ w.ofLp))
    have hchange : star v.ofLp ⬝ᵥ (S *ᵥ w.ofLp) -
        star v.ofLp ⬝ᵥ (T i *ᵥ w.ofLp) =
      star v.ofLp ⬝ᵥ ((S * D i * S) *ᵥ w.ofLp) -
        star v.ofLp ⬝ᵥ ((S * D i * T i * D i * S) *ᵥ w.ofLp) := by
      rw [← dotProduct_sub, ← Matrix.sub_mulVec, hexp i, Matrix.sub_mulVec, dotProduct_sub]
    rw [hprobe, hchange, hleading] at hrev
    exact (by linarith : specNorm S - specNorm (T i) ≤
      ‖star p.ofLp ⬝ᵥ (D i *ᵥ q.ofLp) -
        star v.ofLp ⬝ᵥ ((S * D i * T i * D i * S) *ᵥ w.ofLp)‖).trans
          (norm_sub_le _ _)
  have hb (i : ι) : b i ≤ 2 * R * c ^ 2 * ‖WithLp.toLp 2 (D i *ᵥ q.ofLp)‖ := by
    let x : EuclideanSpace ℂ n := WithLp.toLp 2 ((D i)ᴴ *ᵥ p.ofLp)
    let y : EuclideanSpace ℂ n := WithLp.toLp 2 (T i *ᵥ (D i *ᵥ q.ofLp))
    have he : star v.ofLp ⬝ᵥ ((S * D i * T i * D i * S) *ᵥ w.ofLp) = inner ℂ x y := by
      have hi : inner ℂ x y = star x.ofLp ⬝ᵥ (T i *ᵥ (D i *ᵥ q.ofLp)) :=
        by rw [← WithLp.toLp_ofLp 2 x, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
      rw [hi]
      dsimp [x, p, q]
      simp only [← Matrix.mulVec_mulVec]
      rw [bilinear_move_left S, bilinear_move_left (D i)]
    have hx : ‖x‖ ≤ 2 * R * c :=
      ((D i)ᴴ.l2_opNorm_mulVec p).trans (by
        rw [← specNorm_eq_norm, specNorm_conjTranspose]
        exact mul_le_mul (hD i) hp (norm_nonneg _) (by positivity))
    have hy : ‖y‖ ≤ c * ‖WithLp.toLp 2 (D i *ᵥ q.ofLp)‖ :=
      (T i).l2_opNorm_mulVec (WithLp.toLp 2 (D i *ᵥ q.ofLp)) |>.trans
        (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
    dsimp [b]
    rw [he]
    exact (norm_inner_le_norm x y).trans
      ((mul_le_mul hx hy (norm_nonneg _) (by positivity)).trans_eq (by ring))
  have hpoint (i : ι) : max (specNorm S - specNorm (T i)) 0 ^ 2 ≤
      2 * (a i) ^ 2 + 8 * R ^ 2 * c ^ 4 * ‖WithLp.toLp 2 (D i *ᵥ q.ofLp)‖ ^ 2 := by
    have h1 := (sq_le_sq₀ (le_max_right _ _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (hdiff i)
    have h2 : (a i + b i) ^ 2 ≤ 2 * (a i) ^ 2 + 2 * (b i) ^ 2 := by
      nlinarith [sq_nonneg (a i - b i)]
    have h3 := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (by positivity) (norm_nonneg _))).mpr (hb i)
    nlinarith
  have ha := sum_bilinear_sq_le_mul_bilinearSquareMass D Finset.univ p q hc hp hq
  have hgram := sum_norm_sq_mulVec_le_gram_mul D Finset.univ q
  have hq2 := (sq_le_sq₀ (norm_nonneg q) hc.le).mpr hq
  have hu := hgram.trans
    (mul_le_mul_of_nonneg_left hq2 (specNorm_nonneg _))
  calc _ ≤ ∑ i, (2 * (a i) ^ 2 +
      8 * R ^ 2 * c ^ 4 * ‖WithLp.toLp 2 (D i *ᵥ q.ofLp)‖ ^ 2) :=
        Finset.sum_le_sum (fun i _ => hpoint i)
    _ = 2 * (∑ i, (a i) ^ 2) + 8 * R ^ 2 * c ^ 4 *
        (∑ i, ‖WithLp.toLp 2 (D i *ᵥ q.ofLp)‖ ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (c ^ 4 * bilinearSquareMass D Finset.univ) +
        8 * R ^ 2 * c ^ 4 * (specNorm (∑ i, (D i)ᴴ * D i) * c ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
        (mul_le_mul_of_nonneg_left hu (by positivity))
    _ = _ := by ring

/-- Actual nonreal Hermitian resolvents have their positive coordinate
replacement gradients bounded by the actual computed variance proxy.
The common maximizing probes and the resolvent expansion are proved here. -/
theorem sum_posPart_sq_specNorm_resolvent_sub_le_resolventVarianceProxy [Fintype ι]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (D : ι → Matrix n n ℂ)
    (hD : ∀ i, (D i).IsHermitian) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ i, specNorm (D i) ≤ 2 * R) (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    ∑ i, max (specNorm (resolvent A ζ) - specNorm (resolvent (A - D i) ζ)) 0 ^ 2 ≤
      resolventVarianceProxy D Finset.univ R |ζ.im| := by
  let S := resolvent A ζ
  let T : ι → Matrix n n ℂ := fun i => resolvent (A - D i) ζ
  have hr (B : Matrix n n ℂ) (hB : B.IsHermitian) : ζ ∈ resolventSet ℂ B := by
    change IsUnit (algebraMap ℂ (Matrix n n ℂ) ζ - B)
    simpa only [Algebra.algebraMap_eq_smul_one] using
      hB.isUnit_smul_one_sub_of_im_ne_zero hζ
  have hdiff (i : ι) : S - T i = S * D i * T i := by
    dsimp [S, T]
    rw [spectrum.resolvent_sub_resolvent (hr A hA) (hr (A - D i) (hA.sub (hD i)))]
    have he : A - (A - D i) = D i := by abel
    rw [he]
  have hrev (i : ι) : S - T i = T i * D i * S := by
    have h := spectrum.resolvent_sub_resolvent (hr (A - D i) (hA.sub (hD i))) (hr A hA)
    change T i - S = T i * ((A - D i) - A) * S at h
    have he : (A - D i) - A = -D i := by abel
    rw [he, Matrix.mul_neg, Matrix.neg_mul] at h
    have := congrArg Neg.neg h
    simpa only [neg_sub, neg_neg] using this
  have hexp (i : ι) : S - T i = S * D i * S - S * D i * T i * D i * S := by
    calc S - T i = S * D i * T i := hdiff i
      _ = S * D i * S - S * D i * (S - T i) := by noncomm_ring
      _ = _ := by rw [hrev i]; noncomm_ring
  have h := sum_posPart_sq_le_of_resolvent_expansion S T D
    (inv_pos.mpr (abs_pos.mpr hζ)) hR (hA.specNorm_resolvent_le hζ)
    (fun i => (hA.sub (hD i)).specNorm_resolvent_le hζ) hbound hexp
  simpa only [S, T, resolventVarianceProxy, matrixVarianceProxy, div_eq_mul_inv,
    inv_pow] using h

end NLAlib
