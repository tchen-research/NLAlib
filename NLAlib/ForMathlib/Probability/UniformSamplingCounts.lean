import NLAlib.ForMathlib.Probability.UniformSamplingMarginals
import Mathlib.Analysis.Convex.Jensen

/-!
# Conditional label counts for sampling without replacement

The literal iid/subset coupling has conditional count one for each selected
label and zero outside. These identities prove its barycenter; they are not
assumed as concentration or variance hypotheses. Source: operator re-derivation
`sh:convex-sampling`; supports atlas `srht-ose`.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical
namespace NLAlib

/-- The actual multiplicity of a label in a finite sequence, as a real number.
Source: operator re-derivation `sh:convex-sampling`. -/
def sequenceLabelCount {α : Type*} [DecidableEq α] {k : ℕ} (I : Fin k → α) (j : α) : ℝ :=
  ∑ a, if I a = j then 1 else 0

/-- Summing the actual label multiplicities gives the sequence length.
Source: operator re-derivation `sh:convex-sampling`. -/
theorem sum_sequenceLabelCount {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (I : Fin k → α) : ∑ j, sequenceLabelCount I j = k := by
  unfold sequenceLabelCount
  rw [Finset.sum_comm]
  simp

/-- Simultaneously relabeling a sequence and a label preserves its count.
Source: operator re-derivation `sh:convex-sampling`. -/
theorem sequenceLabelCount_permute {α : Type*} [DecidableEq α] {k : ℕ}
    (σ : Equiv.Perm α) (I : Fin k → α) (j : α) :
    sequenceLabelCount (σ ∘ I) (σ j) = sequenceLabelCount I j := by
  simp only [sequenceLabelCount, Function.comp_apply, σ.injective.eq_iff]

/-- The actual conditional finite weights at a selected exact-size subset.
Source: operator re-derivation `sh:convex-sampling`, using the proved uniform marginal. -/
def iidSubsetConditionalWeight
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (T : ExactRowSubset α k) (I : Fin k → α) : ℝ :=
  (Fintype.card (ExactRowSubset α k) : ℝ) * (iidSubsetJointPMF hk (I, T)).toReal

/-- Conditional weights are nonnegative actual probability masses.
Source: operator re-derivation `sh:convex-sampling`. -/
theorem iidSubsetConditionalWeight_nonneg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (T : ExactRowSubset α k) (I : Fin k → α) :
    0 ≤ iidSubsetConditionalWeight hk T I := by
  unfold iidSubsetConditionalWeight
  positivity

/-- The derived conditional weights sum to one.
Source: operator re-derivation `sh:convex-sampling`, from the actual uniform marginal. -/
theorem sum_iidSubsetConditionalWeight
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (T : ExactRowSubset α k) :
    ∑ I, iidSubsetConditionalWeight hk T I = 1 := by
  have hN : (Fintype.card (ExactRowSubset α k) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨T⟩ : 0 < Fintype.card (ExactRowSubset α k)).ne'
  unfold iidSubsetConditionalWeight
  rw [← Finset.mul_sum]
  change (Fintype.card (ExactRowSubset α k) : ℝ) * iidSubsetMarginal hk T = 1
  rw [iidSubsetMarginal_eq_uniform]
  field_simp

/-- Conditional weights are equivariant under joint label permutations.
Source: operator re-derivation `sh:convex-sampling`. -/
theorem iidSubsetConditionalWeight_invariant
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (σ : Equiv.Perm α)
    (T : ExactRowSubset α k) (I : Fin k → α) :
    iidSubsetConditionalWeight hk (permuteExactRowSubset σ T) (σ ∘ I) =
      iidSubsetConditionalWeight hk T I := by
  simp only [iidSubsetConditionalWeight, iidSubsetJointPMF_toReal_invariant]

/-- The conditional expected multiplicity at one selected subset.
Source: operator re-derivation `sh:convex-sampling`; computed from actual masses. -/
def iidSubsetExpectedCount
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (T : ExactRowSubset α k) (j : α) : ℝ :=
  ∑ I, iidSubsetConditionalWeight hk T I * sequenceLabelCount I j

/-- Expected multiplicities are invariant under relabeling.
Source: operator re-derivation `sh:convex-sampling`. -/
theorem iidSubsetExpectedCount_invariant
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (σ : Equiv.Perm α) (T : ExactRowSubset α k) (j : α) :
    iidSubsetExpectedCount hk (permuteExactRowSubset σ T) (σ j) =
      iidSubsetExpectedCount hk T j := by
  unfold iidSubsetExpectedCount
  rw [← (permuteSequenceEquiv σ).sum_comp]
  change (∑ I, iidSubsetConditionalWeight hk (permuteExactRowSubset σ T) (σ ∘ I) *
      sequenceLabelCount (σ ∘ I) (σ j)) = _
  simp_rw [iidSubsetConditionalWeight_invariant, sequenceLabelCount_permute]

/-- Swapping labels in the same membership region fixes an exact subset.
Source: the stabilizer argument in `sh:convex-sampling`. -/
theorem permuteExactRowSubset_swap_eq
    {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (T : ExactRowSubset α k) (i j : α) (hij : i ∈ T.val ↔ j ∈ T.val) :
    permuteExactRowSubset (Equiv.swap i j) T = T := by
  apply Subtype.ext
  ext a
  simp only [permuteExactRowSubset, Finset.mem_map_equiv, Equiv.symm_swap]
  by_cases hai : a = i
  · subst a; simpa using hij.symm
  · by_cases haj : a = j
    · subst a; simpa using hij
    · simp [Equiv.swap_apply_of_ne_of_ne hai haj]

/-- Every label inside the selected subset has the same expected count.
Source: operator re-derivation `sh:convex-sampling`, swaps within the subset. -/
theorem iidSubsetExpectedCount_eq_of_mem
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (T : ExactRowSubset α k) {i j : α}
    (hi : i ∈ T.val) (hj : j ∈ T.val) :
    iidSubsetExpectedCount hk T i = iidSubsetExpectedCount hk T j := by
  have hh := iidSubsetExpectedCount_invariant hk (Equiv.swap i j) T i
  rw [permuteExactRowSubset_swap_eq T i j (iff_of_true hi hj), Equiv.swap_apply_left] at hh
  exact hh.symm

/-- Outside the selected subset, the conditional count is zero because the
literal coupling always contains the sequence support.
Source: operator re-derivation `sh:convex-sampling`. -/
theorem iidSubsetExpectedCount_eq_zero_of_not_mem
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (T : ExactRowSubset α k) {j : α} (hj : j ∉ T.val) :
    iidSubsetExpectedCount hk T j = 0 := by
  unfold iidSubsetExpectedCount
  apply Finset.sum_eq_zero
  intro I _
  by_cases hq : (iidSubsetJointPMF hk (I, T)).toReal = 0
  · simp [iidSubsetConditionalWeight, hq]
  have hs : Finset.univ.image I ⊆ T.val := by
    by_contra hnot
    exact hq (iidSubsetJointPMF_toReal_eq_zero_of_not_subset hk I T hnot)
  have hc : sequenceLabelCount I j = 0 := by
    unfold sequenceLabelCount
    apply Finset.sum_eq_zero
    intro a _
    have hne : I a ≠ j := by
      intro heq
      apply hj
      rw [← heq]
      exact hs (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
    simp [hne]
  rw [hc, mul_zero]

/-- The conditional count sum still equals the sequence length.
Source: operator re-derivation `sh:convex-sampling`. -/
theorem sum_iidSubsetExpectedCount
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (T : ExactRowSubset α k) :
    ∑ j, iidSubsetExpectedCount hk T j = k := by
  unfold iidSubsetExpectedCount
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_sequenceLabelCount]
  rw [← Finset.sum_mul, sum_iidSubsetConditionalWeight, one_mul]

/-- Each selected label has exact conditional expected count one. This is
proved by exchangeability and the fixed size, rather than assumed.
Source: operator re-derivation `sh:convex-sampling`. -/
theorem iidSubsetExpectedCount_eq_one_of_mem
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ} (hk0 : 0 < k)
    (hk : k ≤ Fintype.card α) (T : ExactRowSubset α k) {i : α} (hi : i ∈ T.val) :
    iidSubsetExpectedCount hk T i = 1 := by
  have hsum : (∑ j ∈ T.val, iidSubsetExpectedCount hk T j) = k := by
    calc
      _ = ∑ j, iidSubsetExpectedCount hk T j := Finset.sum_subset (Finset.subset_univ _)
        (fun j _ hj => iidSubsetExpectedCount_eq_zero_of_not_mem hk T hj)
      _ = _ := sum_iidSubsetExpectedCount hk T
  have heq : (k : ℝ) * iidSubsetExpectedCount hk T i = (k : ℝ) := by
    calc
      _ = ∑ _j ∈ T.val, iidSubsetExpectedCount hk T i := by simp [T.property]
      _ = ∑ j ∈ T.val, iidSubsetExpectedCount hk T j := Finset.sum_congr rfl
        (fun j hj => iidSubsetExpectedCount_eq_of_mem hk T hi hj)
      _ = k := hsum
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  apply mul_left_cancel₀ hkR
  simpa only [mul_one] using heq

/-- A sequence sum is the multiplicity-weighted sum over population labels.
Source: finite bookkeeping in operator re-derivation `sh:convex-sampling`. -/
theorem sum_sequence_eq_sum_count_smul
    {α E : Type*} [Fintype α] [DecidableEq α] [AddCommGroup E] [Module ℝ E]
    {k : ℕ} (I : Fin k → α) (A : α → E) :
    (∑ a, A (I a)) = ∑ j, sequenceLabelCount I j • A j := by
  unfold sequenceLabelCount
  simp only [Finset.sum_smul, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_comm]
  simp

/-- The conditional barycenter of the literal iid sequence sum equals the
unweighted sum over the selected subset.
Source: operator re-derivation `sh:convex-sampling`; all count identities are derived. -/
theorem sum_conditionalWeight_smul_sequence_sum
    {α E : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [AddCommGroup E] [Module ℝ E]
    {k : ℕ} (hk0 : 0 < k) (hk : k ≤ Fintype.card α) (T : ExactRowSubset α k) (A : α → E) :
    (∑ I, iidSubsetConditionalWeight hk T I • ∑ a, A (I a)) = ∑ j ∈ T.val, A j := by
  simp_rw [sum_sequence_eq_sum_count_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  change (∑ j, iidSubsetExpectedCount hk T j • A j) = _
  calc
    _ = ∑ j ∈ T.val, iidSubsetExpectedCount hk T j • A j := (Finset.sum_subset
      (Finset.subset_univ _) (fun j _ hj => by
        rw [iidSubsetExpectedCount_eq_zero_of_not_mem hk T hj, zero_smul])).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [iidSubsetExpectedCount_eq_one_of_mem hk0 hk T hj, one_smul]

end NLAlib
