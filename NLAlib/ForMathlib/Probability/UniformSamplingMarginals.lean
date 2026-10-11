import NLAlib.ForMathlib.Probability.UniformSamplingCoupling

/-!
# Genuine marginals and symmetries of iid/subset sampling

The explicit coupling has iid uniform sequence marginal and uniform exact
subset marginal. Sources: Hoeffding 1963; operator re-derivation `sh:convex-sampling`.
The symmetrized support-extension proof architecture is adapted from Diar
Heidary's MIT-licensed sampling coupling, pinned in UniformSamplingCoupling.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical ENNReal NNReal
namespace NLAlib

/-- Permuting every label gives a bijection of the iid sequence sample space.
Source: the finite coupling in `sh:convex-sampling`. -/
def permuteSequenceEquiv {α : Type*} {k : ℕ} (σ : Equiv.Perm α) :
    (Fin k → α) ≃ (Fin k → α) := Equiv.arrowCongr (Equiv.refl _) σ

/-- The source action changes only its independent uniform permutation.
Source: the finite coupling in `sh:convex-sampling`. -/
def iidSubsetSourceAct {α : Type*} {k : ℕ} (σ : Equiv.Perm α) :
    ((Fin k → α) × Equiv.Perm α) ≃ ((Fin k → α) × Equiv.Perm α) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.mulLeft σ)

/-- The outcome action jointly permutes sequence labels and selected labels.
Source: the finite coupling in `sh:convex-sampling`. -/
def iidSubsetPairAct {α : Type*} [Fintype α] {k : ℕ} (σ : Equiv.Perm α) :
    ((Fin k → α) × ExactRowSubset α k) ≃ ((Fin k → α) × ExactRowSubset α k) :=
  Equiv.prodCongr (permuteSequenceEquiv σ) (permuteExactRowSubsetEquiv σ)

/-- The literal joint coupling is equivariant under every label permutation.
Source: the finite coupling in `sh:convex-sampling`. -/
theorem iidSubsetOutcome_act {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (σ : Equiv.Perm α) (z : (Fin k → α) × Equiv.Perm α) :
    iidSubsetOutcome hk (iidSubsetSourceAct σ z) = iidSubsetPairAct σ (iidSubsetOutcome hk z) := by
  apply Prod.ext
  · funext i
    rfl
  · apply Subtype.ext
    ext i
    simp [iidSubsetOutcome, iidSubsetSourceAct, iidSubsetPairAct,
      permuteExactRowSubsetEquiv, permuteExactRowSubset, Finset.mem_map_equiv]
    rfl

/-- Joint coupling probability masses are invariant under joint label permutations.
Source: the finite coupling in `sh:convex-sampling`. -/
theorem iidSubsetJointPMF_toReal_invariant
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (σ : Equiv.Perm α)
    (I : Fin k → α) (T : ExactRowSubset α k) :
    (iidSubsetJointPMF hk (σ ∘ I, permuteExactRowSubset σ T)).toReal =
      (iidSubsetJointPMF hk (I, T)).toReal := by
  exact toReal_map_pmf_invariant (PMF.uniformOfFintype ((Fin k → α) × Equiv.Perm α))
    (iidSubsetOutcome hk) (iidSubsetSourceAct σ) (iidSubsetPairAct σ)
    (fun z => by simp only [PMF.uniformOfFintype_apply]) (iidSubsetOutcome_act hk σ) (I, T)

/-- The sequence marginal of the explicit joint coupling is genuinely iid uniform,
with mass `1/n^k` for every sequence.
Source: the finite coupling in `sh:convex-sampling`. -/
theorem iidSubsetJointPMF_toReal_first_marginal
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (I : Fin k → α) :
    (∑ T : ExactRowSubset α k, (iidSubsetJointPMF hk (I, T)).toReal) =
      1 / (Fintype.card (Fin k → α) : ℝ) := by
  classical
  let : DecidableEq ((Fin k → α) × ExactRowSubset α k) :=
    fun z w => Classical.propDecidable (z = w)
  have hI : (Fintype.card (Fin k → α) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hP : (Fintype.card (Equiv.Perm α) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [iidSubsetJointPMF, toReal_map_pmf_apply]
  rw [Finset.sum_comm]
  have hinner : ∀ z : (Fin k → α) × Equiv.Perm α,
      (∑ T : ExactRowSubset α k, if iidSubsetOutcome hk z = (I, T) then
        (PMF.uniformOfFintype ((Fin k → α) × Equiv.Perm α) z).toReal else 0) =
      if z.2 ∘ z.1 = I then
        (PMF.uniformOfFintype ((Fin k → α) × Equiv.Perm α) z).toReal else 0 := by
    intro z
    simp only [iidSubsetOutcome, Prod.mk.injEq]
    by_cases hz : z.2 ∘ z.1 = I <;> simp [hz]
  have hstep : (∑ z : (Fin k → α) × Equiv.Perm α,
      ∑ T : ExactRowSubset α k, if iidSubsetOutcome hk z = (I, T) then
        (PMF.uniformOfFintype ((Fin k → α) × Equiv.Perm α) z).toReal else 0) =
      ∑ z : (Fin k → α) × Equiv.Perm α, if z.2 ∘ z.1 = I then
        (PMF.uniformOfFintype ((Fin k → α) × Equiv.Perm α) z).toReal else 0 :=
    Finset.sum_congr rfl (fun z _ => hinner z)
  change (∑ z : (Fin k → α) × Equiv.Perm α,
      ∑ T : ExactRowSubset α k, if iidSubsetOutcome hk z = (I, T) then
        (PMF.uniformOfFintype ((Fin k → α) × Equiv.Perm α) z).toReal else 0) = _
  rw [hstep]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    Fintype.card_prod, Nat.cast_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hperm : ∀ σ : Equiv.Perm α,
      (∑ J : Fin k → α, if σ ∘ J = I then
        ((Fintype.card (Fin k → α) : ℝ) * Fintype.card (Equiv.Perm α))⁻¹ else 0) =
      ((Fintype.card (Fin k → α) : ℝ) * Fintype.card (Equiv.Perm α))⁻¹ := by
    intro σ
    rw [← (permuteSequenceEquiv σ).symm.sum_comp]
    change (∑ J : Fin k → α, if (permuteSequenceEquiv σ) ((permuteSequenceEquiv σ).symm J) = I
      then ((Fintype.card (Fin k → α) : ℝ) * Fintype.card (Equiv.Perm α))⁻¹ else 0) = _
    simp only [Equiv.apply_symm_apply]
    simp
  simp_rw [hperm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The actual subset marginal mass of the iid/subset coupling.
Source: the finite coupling in `sh:convex-sampling`. -/
def iidSubsetMarginal {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (T : ExactRowSubset α k) : ℝ :=
  ∑ I : Fin k → α, (iidSubsetJointPMF hk (I, T)).toReal

/-- The subset marginal is invariant under label permutations.
Source: the finite coupling in `sh:convex-sampling`. -/
theorem iidSubsetMarginal_invariant
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (σ : Equiv.Perm α) (T : ExactRowSubset α k) :
    iidSubsetMarginal hk (permuteExactRowSubset σ T) = iidSubsetMarginal hk T := by
  unfold iidSubsetMarginal
  rw [← (permuteSequenceEquiv σ).sum_comp]
  change (∑ I, (iidSubsetJointPMF hk (σ ∘ I, permuteExactRowSubset σ T)).toReal) = _
  simp_rw [iidSubsetJointPMF_toReal_invariant]

/-- Transitivity makes all exact-size subset marginal masses equal.
Source: the finite coupling in `sh:convex-sampling`. -/
theorem iidSubsetMarginal_eq
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (T U : ExactRowSubset α k) :
    iidSubsetMarginal hk T = iidSubsetMarginal hk U := by
  obtain ⟨σ, hσ⟩ := exists_perm_exactRowSubset T U
  rw [← hσ, iidSubsetMarginal_invariant]

/-- The exact-size subset marginal is genuinely uniform, with the exact
finite uniform mass. Source: the finite coupling in `sh:convex-sampling`. -/
theorem iidSubsetMarginal_eq_uniform
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (T : ExactRowSubset α k) :
    iidSubsetMarginal hk T = 1 / (Fintype.card (ExactRowSubset α k) : ℝ) := by
  have : Nonempty (ExactRowSubset α k) := exactRowSubset_nonempty hk
  have hsum : (∑ U : ExactRowSubset α k, iidSubsetMarginal hk U) = 1 := by
    unfold iidSubsetMarginal
    rw [Finset.sum_comm]
    have hh := sum_toReal_pmf (iidSubsetJointPMF hk)
    rw [Fintype.sum_prod_type] at hh
    exact hh
  have hc : (Fintype.card (ExactRowSubset α k) : ℝ) * iidSubsetMarginal hk T = 1 := by
    calc
      _ = ∑ _U : ExactRowSubset α k, iidSubsetMarginal hk T := by simp
      _ = ∑ U : ExactRowSubset α k, iidSubsetMarginal hk U :=
        Finset.sum_congr rfl (fun U _ => iidSubsetMarginal_eq hk T U)
      _ = 1 := hsum
  have hN : 0 < (Fintype.card (ExactRowSubset α k) : ℝ) := by
    exact_mod_cast (show 0 < Fintype.card (ExactRowSubset α k) from
      Fintype.card_pos_iff.mpr ⟨T⟩)
  apply (eq_div_iff hN.ne').mpr
  simpa only [mul_comm] using hc

end NLAlib
