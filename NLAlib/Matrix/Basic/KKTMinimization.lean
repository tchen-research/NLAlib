import NLAlib.Matrix.Basic.KKT
/-!+# Constrained quadratic minima and the reduced Hessian

Positive definiteness is needed only along feasible directions. Conversely,
uniqueness of the constrained minimum for every right hand side forces that
reduced positive definiteness.

Source: Benzi–Golub–Liesen (2005), §§3.3, 6; re-derivation §39.
Atlas: `kkt-reduced-hessian`.
-/
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {𝕜 : Type*} [RCLike 𝕜] {m n r : Type*}
  [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-- Completing the square needs stationarity only in the chosen feasible
directions. -/
theorem quadraticObjective_add_kernel_of_stationary {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) (Z : Matrix n r 𝕜) (f x : n → 𝕜)
    (hstat : Zᴴ *ᵥ (f - H *ᵥ x) = 0) (y : r → 𝕜) :
    quadraticObjective H f (x + Z *ᵥ y) = quadraticObjective H f x +
      (1 / 2 : ℝ) * RCLike.re (quadForm (reducedHessian H Z) y) := by
  have hc : star f ⬝ᵥ (Z *ᵥ y) = star x ⬝ᵥ (H *ᵥ (Z *ᵥ y)) := by
    have hh := congrArg (fun v => star v ⬝ᵥ y) hstat
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.conjTranspose_conjTranspose] at hh
    simp only [star_sub, sub_dotProduct, star_zero, zero_dotProduct] at hh
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH.eq] at hh
    exact sub_eq_zero.mp hh
  have hq := hH.re_quadForm_smul_add_smul x (Z *ᵥ y) 1 1
  simp only [RCLike.ofReal_one, one_smul, one_pow, one_mul] at hq
  have he : quadForm (reducedHessian H Z) y = quadForm H (Z *ᵥ y) :=
    quadForm_conjTranspose_mul_mul H Z y
  unfold quadraticObjective
  rw [hq, dotProduct_add, map_add, hc, he]
  ring

/-- Reduced positive definiteness makes any stationary feasible point the
unique global constrained minimum, even for an indefinite ambient Hessian.
atlas: kkt-reduced-hessian (partial) -/
theorem IsKernelFrame.quadratic_minimizer_of_reduced_posDef
    {B : Matrix m n 𝕜} {Z : Matrix n r 𝕜} (hZ : IsKernelFrame B Z)
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) (hG : (reducedHessian H Z).PosDef)
    (f x : n → 𝕜) (hstat : Zᴴ *ᵥ (f - H *ᵥ x) = 0) :
    (∀ y, B *ᵥ y = B *ᵥ x → quadraticObjective H f x ≤ quadraticObjective H f y) ∧
      ∀ y, B *ᵥ y = B *ᵥ x →
        quadraticObjective H f y ≤ quadraticObjective H f x → y = x := by
  have he (y : n → 𝕜) (hy : B *ᵥ y = B *ᵥ x) :
      quadraticObjective H f y = quadraticObjective H f x +
        (1 / 2 : ℝ) * RCLike.re (quadForm (reducedHessian H Z) (Zᴴ *ᵥ (y - x))) := by
    have hc := hZ.mulVec_conjTranspose_mulVec (v := y - x)
      (by rw [Matrix.mulVec_sub, hy, sub_self])
    simpa only [hc, add_sub_cancel] using
      quadraticObjective_add_kernel_of_stationary hH Z f x hstat (Zᴴ *ᵥ (y - x))
  constructor
  · intro y hy
    rw [he y hy]
    have hn := hG.posSemidef.re_quadForm_nonneg (Zᴴ *ᵥ (y - x))
    linarith
  · intro y hy hmin
    by_contra hne
    have hc := hZ.mulVec_conjTranspose_mulVec (v := y - x)
      (by rw [Matrix.mulVec_sub, hy, sub_self])
    have hcoord : Zᴴ *ᵥ (y - x) ≠ 0 := by
      intro hz
      rw [hz, Matrix.mulVec_zero] at hc
      exact hne (sub_eq_zero.mp hc.symm)
    have hp := (RCLike.pos_iff.mp (hG.quadForm_pos hcoord)).1
    rw [he y hy] at hmin
    linarith

/-- The minimum property used in the global characterization: feasibility,
global optimality on the affine constraint set, and uniqueness. -/
def IsUniqueConstrainedQuadraticMinimum (H : Matrix n n 𝕜) (B : Matrix m n 𝕜)
    (f : n → 𝕜) (g : m → 𝕜) (x : n → 𝕜) : Prop :=
  B *ᵥ x = g ∧ (∀ y, B *ᵥ y = g → quadraticObjective H f x ≤ quadraticObjective H f y) ∧
    ∀ y, B *ᵥ y = g → quadraticObjective H f y ≤ quadraticObjective H f x → y = x

/-- The null-space inverse formula yields the unique constrained minimum.
atlas: kkt-reduced-hessian (partial) -/
theorem IsKernelFrame.exists_unique_constrained_quadratic_minimum
    {B : Matrix m n 𝕜} {Z : Matrix n r 𝕜} (hZ : IsKernelFrame B Z)
    (hB : IsUnit (B * Bᴴ)) {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    (hG : (reducedHessian H Z).PosDef) (f : n → 𝕜) (g : m → 𝕜) :
    ∃ x, IsUniqueConstrainedQuadraticMinimum H B f g x := by
  let xp := Bᴴ *ᵥ ((B * Bᴴ)⁻¹ *ᵥ g)
  have hxp : B *ᵥ xp = g := by
    dsimp only [xp]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hB), Matrix.one_mulVec]
  let y := (reducedHessian H Z)⁻¹ *ᵥ (Zᴴ *ᵥ (f - H *ᵥ xp))
  have hy : reducedHessian H Z *ᵥ y = Zᴴ *ᵥ (f - H *ᵥ xp) := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit), Matrix.one_mulVec]
  obtain ⟨hx, he⟩ := hZ.kkt_solution hB H f g xp hxp y hy
  have hz : Zᴴ *ᵥ (f - H *ᵥ (xp + Z *ᵥ y)) = 0 := by
    simp only [reducedHessian, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub] at hy
    rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_add]
    linear_combination -hy
  obtain ⟨hmin, huniq⟩ := hZ.quadratic_minimizer_of_reduced_posDef hH hG f _ hz
  exact ⟨xp + Z *ᵥ y, hx, by simpa only [hx] using hmin, by simpa only [hx] using huniq⟩

/-- Necessity already follows from the homogeneous constrained problem:
a unique minimum rules out both negative and flat feasible directions.
atlas: kkt-reduced-hessian (partial) -/
theorem IsKernelFrame.reduced_posDef_of_unique_constrained_minimum_zero
    {B : Matrix m n 𝕜} {Z : Matrix n r 𝕜} (hZ : IsKernelFrame B Z)
    {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    (hmin : ∃ x, IsUniqueConstrainedQuadraticMinimum H B 0 0 x) :
    (reducedHessian H Z).PosDef := by
  obtain ⟨x, hx, hm, hu⟩ := hmin
  have hneg : quadraticObjective H 0 (-x) = quadraticObjective H 0 x := by
    have hq : quadForm H (-x) = quadForm H x := by
      rw [show -x = (-1 : 𝕜) • x by simp, quadForm_smul]
      simp
    simp only [quadraticObjective, hq, star_zero, zero_dotProduct, map_zero, sub_zero]
  have hxneg : -x = x := hu (-x) (by rw [Matrix.mulVec_neg, hx, neg_zero]) (by rw [hneg])
  have hx0 : x = 0 := by
    ext i
    have hi := congrFun hxneg i
    change -(x i) = x i at hi
    have hz : (2 : 𝕜) * x i = 0 := by linear_combination -hi
    exact (_root_.mul_eq_zero.mp hz).resolve_left (by norm_num)
  subst x
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨Matrix.isHermitian_conjTranspose_mul_mul Z hH, ?_⟩
  intro y hy
  have hz : Z *ᵥ y ≠ 0 := by
    intro he
    have hh := congrArg (fun v => Zᴴ *ᵥ v) he
    rw [Matrix.mulVec_mulVec, hZ.orth.conjTranspose_mul_self, Matrix.one_mulVec,
      Matrix.mulVec_zero] at hh
    exact hy hh
  have hfeas : B *ᵥ (Z *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec, hZ.mul_eq_zero, Matrix.zero_mulVec]
  have hn := hm (Z *ᵥ y) hfeas
  have hstrict : quadraticObjective H 0 0 < quadraticObjective H 0 (Z *ᵥ y) := by
    exact lt_of_le_of_ne hn (fun he => hz (hu _ hfeas he.symm.le))
  have hq := quadForm_conjTranspose_mul_mul H Z y
  have hre : 0 < RCLike.re (quadForm (reducedHessian H Z) y) := by
    change quadForm (reducedHessian H Z) y = _ at hq
    simp only [quadraticObjective, star_zero, zero_dotProduct, map_zero,
      quadForm_zero_right, mul_zero, sub_zero] at hstrict
    rw [← hq] at hstrict
    linarith
  have hGH : (reducedHessian H Z).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul Z hH
  change 0 < quadForm (reducedHessian H Z) y
  rw [← hGH.ofReal_re_quadForm y]
  exact RCLike.ofReal_pos.mpr hre

/-- Reduced positive definiteness is equivalent to unique constrained
quadratic minimization for every pair of right hand sides.
atlas: kkt-reduced-hessian (partial) -/
theorem IsKernelFrame.reduced_posDef_iff_unique_constrained_minimum
    {B : Matrix m n 𝕜} {Z : Matrix n r 𝕜} (hZ : IsKernelFrame B Z)
    (hB : IsUnit (B * Bᴴ)) {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    (reducedHessian H Z).PosDef ↔
      ∀ (f : n → 𝕜) (g : m → 𝕜), ∃ x, IsUniqueConstrainedQuadraticMinimum H B f g x := by
  constructor
  · exact fun hG => hZ.exists_unique_constrained_quadratic_minimum hB hH hG
  · intro hh
    exact hZ.reduced_posDef_of_unique_constrained_minimum_zero hH (hh 0 0)

end NLAlib
