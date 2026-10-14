import NLAlib.Polynomial.Quadrature.EndpointJacobiData

/-! # Simplicity and positive weights of constructed endpoint matrix rules

The leading moment Jacobi matrix is unreduced. Radau keeps its actual last coupling;
the Lobatto endpoint shifts prove a positive new square-root coupling. The actual
first-coordinate spectral rules therefore have simple nodes and positive weights.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix

namespace NLAlib

private theorem moment_hierarchy_of_le_support {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {N : ℕ} (hs : (N : ℕ∞) ≤ μ.support.encard) :
    (∀ k ≤ N, hankelMomentDet (polynomialIntegral μ hμ) k ≠ 0) ∧
      (∀ k < N, 0 < orthogonalPolynomialNorm (polynomialIntegral μ hμ) k) :=
  ⟨fun k hk => hankelMomentDet_ne_zero_of_le_support_encard μ hμ
      ((by exact_mod_cast hk : (k : ℕ∞) ≤ N).trans hs),
    fun k hk => orthogonalPolynomialNorm_pos_of_lt_support_encard μ hμ
      ((by exact_mod_cast Nat.succ_le_of_lt hk : (k + 1 : ℕ∞) ≤ N).trans hs)⟩

private theorem radau_border_shape_and_superdiagonal {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {q : ℕ} (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (d : ℝ) :
    let L := polynomialIntegral μ hμ
    let J := orthogonalPolynomialJacobiMatrix L q
    let v := momentJacobiLastCoupling L q
    IsTridiagonal (finSymmetricBorder J v d) ∧
      ∀ i j : Fin (q + 1), i.val + 1 = j.val → finSymmetricBorder J v d i j ≠ 0 := by
  dsimp only
  let L := polynomialIntegral μ hμ
  obtain ⟨hL, hH⟩ := moment_hierarchy_of_le_support hμ hs
  have hLq (k : ℕ) (hk : k ≤ q) : hankelMomentDet L k ≠ 0 := hL k (by change k ≤ q + 1; omega)
  have hHq (k : ℕ) (hk : k < q) : 0 < orthogonalPolynomialNorm L k := hH k (by change k < q + 1; omega)
  have htri := isTridiagonal_orthogonalPolynomialJacobiMatrix L q hLq
  have hv (i : Fin q) (hi : i.val + 1 < q) : momentJacobiLastCoupling L q i = 0 :=
    orthogonalPolynomialJacobiMatrix_apply_eq_zero L hL i.castSucc (Fin.last q) hi
  refine ⟨isTridiagonal_finSymmetricBorder htri hv d,
    finSymmetricBorder_superdiagonal_ne_zero d ?_ ?_⟩
  · intro i j hij
    exact (orthogonalPolynomialJacobiMatrix_superdiagonal_pos L hLq hHq i j hij).ne'
  · intro i hi
    exact (orthogonalPolynomialJacobiMatrix_superdiagonal_pos L hL hH i.castSucc
      (Fin.last q) hi).ne'

/-- The actual left and right Radau rules have distinct nodes and strictly positive
weights throughout the original moment hierarchy, including the one-node case.
Source: focused mathematical reroutes, Section 3 (BL11).
atlas: gauss-radau-lobatto (partial) -/
theorem radauNodes_injective_and_weights_pos {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (q : ℕ) (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (a c : ℝ) :
    let L := polynomialIntegral μ hμ
    Function.Injective (leftRadauNodes L q a) ∧ (∀ i, 0 < leftRadauWeights L q a i) ∧
      Function.Injective (rightRadauNodes L q c) ∧ ∀ i, 0 < rightRadauWeights L q c i := by
  dsimp only
  let L := polynomialIntegral μ hμ
  have hmass : 0 < L 1 := by
    simpa only [L, polynomialIntegral_apply, eval_one] using integral_one_pos_of_one_le_support_encard
      hμ ((by exact_mod_cast (show 1 ≤ q + 1 by omega) : (1 : ℕ∞) ≤ q + 1).trans hs)
  obtain ⟨hltri, hlsub⟩ := radau_border_shape_and_superdiagonal hμ hs
    (leftRadauCorner (orthogonalPolynomialJacobiMatrix L q) (momentJacobiLastCoupling L q) a)
  obtain ⟨hrtri, hrsub⟩ := radau_border_shape_and_superdiagonal hμ hs
    (rightRadauCorner (orthogonalPolynomialJacobiMatrix L q) (momentJacobiLastCoupling L q) c)
  obtain ⟨hln, hlw⟩ := rootedMatrixRule_nodes_injective_and_weights_pos (Nat.succ_pos q)
    (isHermitian_leftRadauJacobiMatrix L q a) hltri hlsub hmass
  obtain ⟨hrn, hrw⟩ := rootedMatrixRule_nodes_injective_and_weights_pos (Nat.succ_pos q)
    (isHermitian_rightRadauJacobiMatrix L q c) hrtri hrsub hmass
  exact ⟨hln, hlw, hrn, hrw⟩

/-- The actual Lobatto rule has distinct nodes and strictly positive weights under
the exact positive endpoint-shift hypotheses. The original measure only needs the
displayed `(q+1)` moment hierarchy. Source: focused reroutes, Section 3 (BL7), (BL11).
atlas: gauss-radau-lobatto (partial) -/
theorem lobattoNodes_injective_and_weights_pos {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (q : ℕ) (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (a c : ℝ) (hac : a < c)
    (hJa : (orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) (q + 1) - a • 1).PosDef)
    (hJc : (c • 1 - orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) (q + 1)).PosDef) :
    let L := polynomialIntegral μ hμ
    Function.Injective (lobattoNodes L q a c) ∧ ∀ i, 0 < lobattoWeights L q a c i := by
  dsimp only
  let L := polynomialIntegral μ hμ
  let J := orthogonalPolynomialJacobiMatrix L (q + 1)
  let e : Fin (q + 1) → ℝ := Pi.single (Fin.last q) 1
  let v := Real.sqrt (lobattoCouplingSq J e a c) • e
  have he : e ≠ 0 := by intro hz; have := congrFun hz (Fin.last q); simp [e] at this
  have hγ := lobattoCouplingSq_pos hac hJa hJc he
  have hv (i : Fin (q + 1)) (hi : i.val + 1 < q + 1) : v i = 0 := by
    have hne : i ≠ Fin.last q := by intro hz; have := congrArg Fin.val hz; simp at this; omega
    simp [v, e, hne]
  obtain ⟨hL, hH⟩ := moment_hierarchy_of_le_support hμ hs
  have htri := isTridiagonal_finSymmetricBorder
    (isTridiagonal_orthogonalPolynomialJacobiMatrix L (q + 1) hL) hv (lobattoCorner J e a c)
  have hsub := finSymmetricBorder_superdiagonal_ne_zero (lobattoCorner J e a c)
    (fun i j hij => (orthogonalPolynomialJacobiMatrix_superdiagonal_pos L hL hH i j hij).ne')
    (v := v) (by
      intro i hi
      have hilast : i = Fin.last q := Fin.ext (by simpa using (show i.val = q by omega))
      subst i
      simpa only [v, e, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] using
        (Real.sqrt_pos.mpr hγ).ne')
  have hmass : 0 < L 1 := by
    simpa only [L, polynomialIntegral_apply, eval_one] using integral_one_pos_of_one_le_support_encard
      hμ ((by exact_mod_cast (show 1 ≤ q + 1 by omega) : (1 : ℕ∞) ≤ q + 1).trans hs)
  exact rootedMatrixRule_nodes_injective_and_weights_pos (by omega : 0 < q + 2)
    (isHermitian_lobattoJacobiMatrix L q a c) htri hsub hmass

end NLAlib
