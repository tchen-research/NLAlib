import NLAlib.Matrix.Functions.SchattenDualTestMatrix
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multilinear Schatten interpolation from the nuclear/spectral endpoints

The functional is arbitrary and complex multilinear; no trace representation
or interpolation conclusion is supplied as data.

The real exponent vectors with a uniform imaginary-tube bound form a convex
set by scalar Hadamard three-lines. Its vertices are the given nuclear/spectral
endpoints. Convex.sum_mem gives all finite positive Schatten exponents in one
step, avoiding recursive currying and all divisions by singular values.
Zero singular directions are identically zero entire functions.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 5.2, q=infinity
endpoint specialization used in Proposition 5.1. Finite exponents and infinity
exponents are included. Infinity arguments remain fixed while the tube proof
interpolates only the positive reciprocal coordinates.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Matrix
namespace NLAlib

/-- A scalar holomorphic tube bound propagates from the simplex vertices to
all nonnegative barycentric exponent vectors. The proof is ordinary three-lines;
it permits C=0 and includes the degenerate finite simplex. -/
private theorem norm_le_of_simplex_tube_vertices
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℂ) → ℂ) (hg : Differentiable ℂ g) {C B : ℝ} (hC : 0 ≤ C)
    (hB : ∀ z : ι → ℂ, (∀ i, 0 ≤ (z i).re) → ‖g z‖ ≤ B)
    (θ : ι → ℝ) (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = 1)
    (hvertex : ∀ j, θ j ≠ 0 → ∀ t : ι → ℝ,
      ‖g (fun i => (((Pi.single j (1 : ℝ) : ι → ℝ) i : ℝ) : ℂ) + (t i : ℂ) * Complex.I)‖ ≤ C) :
    ‖g (fun i => (θ i : ℂ))‖ ≤ C := by
  let S : Set (ι → ℝ) := {a | (∀ i, 0 ≤ a i) ∧ ∀ t : ι → ℝ,
    ‖g (fun i => (a i : ℂ) + (t i : ℂ) * Complex.I)‖ ≤ C}
  have hconvex : Convex ℝ S := by
    intro a ha b hb x y hx hy hxy
    refine ⟨?_, ?_⟩
    · intro i
      exact add_nonneg (mul_nonneg hx (ha.1 i)) (mul_nonneg hy (hb.1 i))
    · intro t
      let Γ : ℂ → ι → ℂ := fun z i =>
        (1 - z) * (a i : ℂ) + z * (b i : ℂ) + (t i : ℂ) * Complex.I
      let f : ℂ → ℂ := g ∘ Γ
      have hΓ : Differentiable ℂ Γ := by
        dsimp [Γ]
        fun_prop
      have hf : Differentiable ℂ f := hg.comp hΓ
      have hbounded : BddAbove ((norm ∘ f) ''
          Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
        refine ⟨B, ?_⟩
        rintro _ ⟨z, hz, rfl⟩
        apply hB
        intro i
        dsimp [Γ]
        simp only [Complex.mul_re, Complex.sub_re,
          Complex.one_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        exact add_nonneg (mul_nonneg (sub_nonneg.mpr hz.2) (ha.1 i))
          (mul_nonneg hz.1 (hb.1 i))
      have hleft : ∀ z ∈ Complex.re ⁻¹' {(0 : ℝ)}, ‖f z‖ ≤ C := by
        intro z hz
        have hz0 : z.re = 0 := hz
        have he : Γ z = fun i => (a i : ℂ) +
            ((t i + z.im * (b i - a i) : ℝ) : ℂ) * Complex.I := by
          ext i
          apply Complex.ext <;> simp [Γ, hz0]
          ring
        simpa only [f, Function.comp_apply, he] using
          ha.2 (fun i => t i + z.im * (b i - a i))
      have hright : ∀ z ∈ Complex.re ⁻¹' {(1 : ℝ)}, ‖f z‖ ≤ C := by
        intro z hz
        have hz1 : z.re = 1 := hz
        have he : Γ z = fun i => (b i : ℂ) +
            ((t i + z.im * (b i - a i) : ℝ) : ℂ) * Complex.I := by
          ext i
          apply Complex.ext <;> simp [Γ, hz1]
          ring
        simpa only [f, Function.comp_apply, he] using
          hb.2 (fun i => t i + z.im * (b i - a i))
      have hy1 : y ≤ 1 := by linarith
      have hstrip : (y : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 :=
        ⟨by simpa using hy, by simpa using hy1⟩
      have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
        f hstrip ⟨hf.differentiableOn, hf.continuous.continuousOn⟩ hbounded hleft hright
      have hc : C ^ (1 - y) * C ^ y = C := by
        rw [← Real.rpow_add_of_nonneg hC (sub_nonneg.mpr hy1) hy]
        simp
      simp only [Complex.ofReal_re, hc] at h
      have he : Γ (y : ℂ) = fun i =>
          (((x • a + y • b) i : ℝ) : ℂ) + (t i : ℂ) * Complex.I := by
        ext i
        have hxa : x = 1 - y := by linarith
        subst x
        simp [Γ, Pi.smul_apply, smul_eq_mul]
      simpa only [f, Function.comp_apply, he] using h
  let T : Finset ι := Finset.univ.filter (fun j => θ j ≠ 0)
  have hv : ∀ j ∈ T, (Pi.single j (1 : ℝ) : ι → ℝ) ∈ S := by
    intro j hj
    refine ⟨fun i => by simp [Pi.single_apply]; split_ifs <;> norm_num, ?_⟩
    exact hvertex j (Finset.mem_filter.mp hj).2
  have hsumT : ∑ j ∈ T, θ j = 1 := by
    calc
      _ = ∑ j, θ j := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hj
        have hz : θ j = 0 := by simpa [T] using hj
        exact hz
      _ = 1 := hsum
  have hcomb := hconvex.sum_mem (t := T) (w := θ)
    (fun i _ => hθ i) hsumT hv
  have hfull : (∑ j ∈ T, θ j • (Pi.single j (1 : ℝ) : ι → ℝ)) =
      ∑ j, θ j • (Pi.single j (1 : ℝ) : ι → ℝ) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hz : θ j = 0 := by simpa [T] using hj
    simp [hz]
  rw [hfull] at hcomb
  have he : (∑ j, θ j • (Pi.single j (1 : ℝ) : ι → ℝ)) = θ := by
    ext i
    simp [Pi.single_apply]
  rw [he] at hcomb
  simpa only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, add_zero] using
    hcomb.2 (0 : ι → ℝ)

/-- Zero-safe entire singular coefficient for exponent interpolation. -/
private def schattenSimplexCoefficient (p w : ℝ) (z : ℂ) : ℂ :=
  schattenDualTestCoefficient 1 0 w (-(p : ℂ) * z)

private theorem differentiable_schattenSimplexCoefficient (p w : ℝ) :
    Differentiable ℂ (schattenSimplexCoefficient p w) := by
  unfold schattenSimplexCoefficient
  fun_prop

private theorem norm_schattenSimplexCoefficient_of_pos {w : ℝ} (hw : 0 < w)
    (p : ℝ) (z : ℂ) :
    ‖schattenSimplexCoefficient p w z‖ = w ^ (p * z.re) := by
  rw [schattenSimplexCoefficient, norm_schattenDualTestCoefficient_of_pos hw]
  congr 1
  simp

private theorem norm_schattenSimplexCoefficient_le_one {p w : ℝ}
    (hp : 0 ≤ p) (hw : w ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖schattenSimplexCoefficient p w z‖ ≤ 1 := by
  by_cases hwpos : 0 < w
  · rw [norm_schattenSimplexCoefficient_of_pos hwpos]
    exact Real.rpow_le_one hw.1 hw.2 (mul_nonneg hp hz)
  · simp [schattenSimplexCoefficient, schattenDualTestCoefficient, hwpos]

private theorem norm_schattenSimplexCoefficient_one {p w : ℝ}
    (hp : 0 < p) (hw : 0 ≤ w) {z : ℂ} (hz : z.re = 1) :
    ‖schattenSimplexCoefficient p w z‖ = w ^ p := by
  by_cases hwpos : 0 < w
  · rw [norm_schattenSimplexCoefficient_of_pos hwpos, hz, mul_one]
  · have hwzero : w = 0 := le_antisymm (not_lt.mp hwpos) hw
    subst w
    simp [schattenSimplexCoefficient, schattenDualTestCoefficient, Real.zero_rpow hp.ne']

private theorem schattenSimplexCoefficient_center {p w : ℝ}
    (hp : 0 < p) (hw : 0 ≤ w) :
    schattenSimplexCoefficient p w ((1 / p : ℝ) : ℂ) = (w : ℂ) := by
  by_cases hwpos : 0 < w
  · rw [schattenSimplexCoefficient, schattenDualTestCoefficient, if_pos hwpos]
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    simp only [Complex.ofReal_zero, Complex.ofReal_one]
    have he : ((0 : ℂ) - (-(p : ℂ) * ((1 / p : ℝ) : ℂ))) / 1 = 1 := by
      push_cast
      field_simp
      ring
    rw [he, one_mul, ← Complex.ofReal_exp, Real.exp_log hwpos]
  · have hwzero : w = 0 := le_antisymm (not_lt.mp hwpos) hw
    subst w
    simp [schattenSimplexCoefficient, schattenDualTestCoefficient]

private def schattenSimplexMatrix {n : Type*} [Fintype n]
    (U V : Matrix n (Fin (Fintype.card n)) ℂ) (p : ℝ)
    (w : Fin (Fintype.card n) → ℝ) (z : ℂ) : Matrix n n ℂ :=
  U * Matrix.diagonal (fun l => schattenSimplexCoefficient p (w l) z) * Vᴴ

open scoped Matrix.Norms.L2Operator in
private theorem differentiable_schattenSimplexMatrix
    {n : Type*} [Fintype n] [DecidableEq n]
    (U V : Matrix n (Fin (Fintype.card n)) ℂ) (p : ℝ)
    (w : Fin (Fintype.card n) → ℝ) :
    Differentiable ℂ (schattenSimplexMatrix U V p w) := by
  change Differentiable ℂ (fun z => schattenDualTestMatrix V U 1 0 w (-(p : ℂ) * z))
  fun_prop

open scoped Matrix.Norms.L2Operator in
private theorem specNorm_schattenSimplexMatrix_le_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {U V : Matrix n (Fin (Fintype.card n)) ℂ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) {p : ℝ}
    (hp : 0 ≤ p) {w : Fin (Fintype.card n) → ℝ}
    (hw : ∀ l, w l ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : 0 ≤ z.re) :
    specNorm (schattenSimplexMatrix U V p w z) ≤ 1 := by
  rw [schattenSimplexMatrix, specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hV,
    specNorm_mul_left_of_hasOrthonormalCols hU, specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun l =>
    norm_schattenSimplexCoefficient_le_one hp (hw l) hz

private theorem nuclearNorm_schattenSimplexMatrix_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {U V : Matrix n (Fin (Fintype.card n)) ℂ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) {p : ℝ}
    (hp : 0 < p) {w : Fin (Fintype.card n) → ℝ} (hw : ∀ l, 0 ≤ w l)
    (hpower : ∑ l, w l ^ p = 1) {z : ℂ} (hz : z.re = 1) :
    nuclearNorm (schattenSimplexMatrix U V p w z) = 1 := by
  rw [← schattenNormReal_one, schattenSimplexMatrix,
    schattenNormReal_isometry_mul_mul_conjTranspose hU hV,
    schattenNormReal_diagonal_complex]
  simp only [Real.rpow_one, one_div_one]
  simp_rw [norm_schattenSimplexCoefficient_one hp (hw _) hz]
  exact hpower

private theorem IsSVD.schattenSimplexMatrix_center
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} {U V : Matrix n (Fin (Fintype.card n)) ℂ}
    (h : IsSVD A U V) {p : ℝ} (hp : 0 < p) :
    schattenSimplexMatrix U V p
      (fun l => singularValues A l / schattenNormReal A p) ((1 / p : ℝ) : ℂ) =
      ((schattenNormReal A p : ℂ)⁻¹) • A := by
  have hd : Matrix.diagonal (fun l : Fin (Fintype.card n) =>
      schattenSimplexCoefficient p (singularValues A l / schattenNormReal A p)
        ((1 / p : ℝ) : ℂ)) =
      ((schattenNormReal A p : ℂ)⁻¹) •
        (rectDiag (singularValues A) : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, rectDiag_apply_ofReal,
        smul_eq_mul]
      rw [schattenSimplexCoefficient_center hp
        (div_nonneg (singularValues_nonneg A i) (schattenNormReal_nonneg _ _))]
      push_cast
      exact mul_comm _ _
    · have hv : (i : ℕ) ≠ j := fun he => hij (Fin.ext he)
      simp [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply,
        rectDiag_apply_ofReal, hv, smul_eq_mul]
  rw [schattenSimplexMatrix, hd, Matrix.mul_smul, Matrix.smul_mul, ← h.eq]

open scoped Matrix.Norms.L2Operator ENNReal in
/-- Full nuclear/spectral endpoint interpolation, including infinity Schatten
exponents. Reciprocal infinity exponents contribute zero to the real simplex;
the corresponding normalized matrices remain fixed throughout the analytic
interpolation. The conclusion uses the native unnormalized Schatten norms. -/
theorem norm_multilinear_le_prod_schattenNorm_of_endpoints
    {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (F : ContinuousMultilinearMap ℂ (fun _ : ι => Matrix n n ℂ) ℂ)
    {C : ℝ} (hC : 0 ≤ C)
    (hendpoint : ∀ j (M : ι → Matrix n n ℂ),
      ‖F M‖ ≤ C * nuclearNorm (M j) * ∏ i ∈ Finset.univ.erase j, specNorm (M i))
    (p : ι → ℝ≥0∞) (hp : ∀ i, 1 ≤ p i)
    (hsum : ∑ i, ((p i)⁻¹).toReal = 1) (M : ι → Matrix n n ℂ) :
    ‖F M‖ ≤ C * ∏ i, schattenNorm (M i) (p i) := by
  classical
  let θ : ι → ℝ := fun i => ((p i)⁻¹).toReal
  let q : ι → ℝ := fun i => (p i).toReal
  have hq (i : ι) (hi : p i ≠ ∞) : 1 ≤ q i := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hi (hp i)
  have hq0 (i : ι) (hi : p i ≠ ∞) : 0 < q i := lt_of_lt_of_le zero_lt_one (hq i hi)
  have hθtop (i : ι) (hi : p i = ∞) : θ i = 0 := by simp [θ, hi]
  have hθq (i : ι) : θ i = 1 / q i := by simp [θ, q, ENNReal.toReal_inv, one_div]
  by_cases hzero : ∃ i, M i = 0
  · obtain ⟨i, hi⟩ := hzero
    rw [F.map_coord_zero i hi, norm_zero]
    exact mul_nonneg hC (Finset.prod_nonneg fun j _ => schattenNorm_nonneg _ _)
  have hM : ∀ i, M i ≠ 0 := by simpa using hzero
  choose U V hUV using (fun i => exists_isSVD (M i))
  let s : ι → ℝ := fun i => schattenNorm (M i) (p i)
  have hsfinite (i : ι) (hi : p i ≠ ∞) : s i = schattenNormReal (M i) (q i) :=
    schattenNorm_eq_of_ne_top (M i) hi
  have hstop (i : ι) (hi : p i = ∞) : s i = specNorm (M i) := by
    simp only [s, hi, schattenNorm_top]
  have hs (i : ι) : 0 < s i := by
    by_cases hi : p i = ∞
    · rw [hstop i hi, specNorm_eq_norm]
      exact norm_pos_iff.mpr (hM i)
    · rw [hsfinite i hi]
      exact schattenNormReal_pos (M i) (hq0 i hi) (hM i)
  let w : ι → Fin (Fintype.card n) → ℝ := fun i l => singularValues (M i) l / s i
  let A : ι → ℂ → Matrix n n ℂ := fun i z =>
    if p i = ∞ then ((s i : ℂ)⁻¹) • M i
    else schattenSimplexMatrix (U i) (V i) (q i) (w i) z
  have hw (i : ι) (hi : p i ≠ ∞) (l : Fin (Fintype.card n)) : w i l ∈ Icc (0 : ℝ) 1 := by
    rw [show w i l = singularValues (M i) l / schattenNormReal (M i) (q i) by
      dsimp only [w]
      rw [hsfinite i hi]]
    exact singularValues_div_schattenNormReal_mem_Icc (M i) (hq0 i hi) (hM i) l
  have hpower (i : ι) (hi : p i ≠ ∞) : ∑ l, w i l ^ q i = 1 := by
    have h := sum_singularValues_div_schattenNormReal_rpow_eq_one (M i) (hq0 i hi) (hM i)
    simpa only [min_self, ← Fin.sum_univ_eq_sum_range, w, hsfinite i hi] using h
  have hAnorm (i : ι) (z : ℂ) (hz : 0 ≤ z.re) : specNorm (A i z) ≤ 1 := by
    by_cases hi : p i = ∞
    · simp only [A, if_pos hi, specNorm_eq_norm, norm_smul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg (hs i).le]
      rw [← specNorm_eq_norm, ← hstop i hi]
      exact (inv_mul_cancel₀ (hs i).ne').le
    · simp only [A, if_neg hi]
      exact specNorm_schattenSimplexMatrix_le_one (hUV i).conjTranspose_mul_left
        (hUV i).conjTranspose_mul_right (hq0 i hi).le (hw i hi) hz
  have hAnuclear (i : ι) (hi : p i ≠ ∞) (z : ℂ) (hz : z.re = 1) :
      nuclearNorm (A i z) = 1 := by
    simp only [A, if_neg hi]
    exact nuclearNorm_schattenSimplexMatrix_one (hUV i).conjTranspose_mul_left
      (hUV i).conjTranspose_mul_right (hq0 i hi) (fun l => (hw i hi l).1)
      (hpower i hi) hz
  let g : (ι → ℂ) → ℂ := fun z => F (fun i => A i (z i))
  have hg : Differentiable ℂ g := by
    have hF : Differentiable ℂ F := fun x => (F.hasFDerivAt x).differentiableAt
    apply hF.comp
    apply differentiable_pi.mpr
    intro i
    by_cases hi : p i = ∞
    · simp only [A, if_pos hi]
      exact differentiable_const _
    · simp only [A, if_neg hi]
      exact (differentiable_schattenSimplexMatrix (U i) (V i) (q i) (w i)).comp
        (differentiable_apply i)
  have hB : ∀ z : ι → ℂ, (∀ i, 0 ≤ (z i).re) → ‖g z‖ ≤ ‖F‖ := by
    intro z hz
    simpa only [Finset.prod_const_one, mul_one] using
      F.le_opNorm_mul_prod_of_le (b := fun _ => (1 : ℝ))
        (fun i => by simpa only [← specNorm_eq_norm] using hAnorm i (z i) (hz i))
  have hvertex : ∀ j, θ j ≠ 0 → ∀ t : ι → ℝ,
      ‖g (fun i => (((Pi.single j (1 : ℝ) : ι → ℝ) i : ℝ) : ℂ) + (t i : ℂ) * Complex.I)‖ ≤ C := by
    intro j hj t
    have hjfin : p j ≠ ∞ := fun ht => hj (hθtop j ht)
    let X : ι → Matrix n n ℂ := fun i =>
      A i ((((Pi.single j (1 : ℝ) : ι → ℝ) i : ℝ) : ℂ) + (t i : ℂ) * Complex.I)
    have hX (i : ι) : specNorm (X i) ≤ 1 := by
      apply hAnorm
      simp [Pi.single_apply]
      split_ifs <;> norm_num
    have hjn : nuclearNorm (X j) = 1 := by
      apply hAnuclear j hjfin
      simp
    calc
      _ ≤ C * nuclearNorm (X j) * ∏ i ∈ Finset.univ.erase j, specNorm (X i) := hendpoint j X
      _ = C * ∏ i ∈ Finset.univ.erase j, specNorm (X i) := by rw [hjn, mul_one]
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left
        (Finset.prod_le_one (fun i _ => specNorm_nonneg _) (fun i _ => hX i)) hC
      _ = C := mul_one _
  have hcenter := norm_le_of_simplex_tube_vertices g hg hC hB θ
    (fun i => ENNReal.toReal_nonneg) hsum hvertex
  have hAcenter (i : ι) : A i (θ i : ℂ) = ((s i : ℂ)⁻¹) • M i := by
    by_cases hi : p i = ∞
    · simp only [A, if_pos hi]
    · simp only [A, if_neg hi, hθq]
      simpa only [w, hsfinite i hi] using (hUV i).schattenSimplexMatrix_center (hq0 i hi)
  have heval : g (fun i => (θ i : ℂ)) = (∏ i, ((s i : ℂ)⁻¹)) • F M := by
    simp only [g, hAcenter]
    exact F.map_smul_univ _ _
  rw [heval, norm_smul, norm_prod] at hcenter
  have hnorm (i : ι) : ‖((s i : ℂ)⁻¹)‖ = (s i)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (hs i).le]
  simp_rw [hnorm] at hcenter
  rw [Finset.prod_inv_distrib] at hcenter
  have hprod : 0 < ∏ i, s i := Finset.prod_pos fun i _ => hs i
  apply (div_le_iff₀ hprod).mp
  simpa only [div_eq_mul_inv, mul_comm] using hcenter


open scoped Matrix.Norms.L2Operator ENNReal in
/-- An arbitrary continuous complex multilinear functional bounded at every
nuclear/spectral endpoint satisfies the sharp finite-exponent Schatten bound.
The library Schatten norms and the endpoint nuclear norm are unnormalized;
there is no dimension factor. Zero matrices and singular directions are included.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 5.2 (q=infinity
simplex used in Proposition 5.1). -/
theorem norm_multilinear_le_prod_schattenNormReal_of_endpoints
    {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (F : ContinuousMultilinearMap ℂ (fun _ : ι => Matrix n n ℂ) ℂ)
    {C : ℝ} (hC : 0 ≤ C)
    (hendpoint : ∀ j (M : ι → Matrix n n ℂ),
      ‖F M‖ ≤ C * nuclearNorm (M j) * ∏ i ∈ Finset.univ.erase j, specNorm (M i))
    (p : ι → ℝ) (hp : ∀ i, 1 ≤ p i) (hsum : ∑ i, 1 / p i = 1)
    (M : ι → Matrix n n ℂ) :
    ‖F M‖ ≤ C * ∏ i, schattenNormReal (M i) (p i) := by
  have hp0 (i : ι) : 0 ≤ p i := le_trans zero_le_one (hp i)
  have hp' (i : ι) : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (p i) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hp i)
  have hsum' : ∑ i, ((ENNReal.ofReal (p i))⁻¹).toReal = 1 := by
    simpa only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (hp0 _), one_div] using hsum
  have h := norm_multilinear_le_prod_schattenNorm_of_endpoints F hC hendpoint
    (fun i => ENNReal.ofReal (p i)) hp' hsum' M
  simpa only [schattenNorm_ofReal _ (hp0 _)] using h

end NLAlib
