/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.DirectionalMarkedReindexing

set_option autoImplicit false

/-!
# Directional supported occupation energy

Grade support, homogeneity, and occupation-weighted marked-energy estimates.
Ported from `SparseFockFormal.DirectionalConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock

namespace DirectionalConcrete

open ParsevalFrame LocalOperator BandInventory FiniteOperator ExternalOperator
  GlobalBands NamedBands FiniteHilbert
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- A concrete full coordinate vector is supported on one exact occupation
grade.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def SupportedAtGrade (nu : ℕ) (x : Fin d × Pattern m n → ℝ) : Prop :=
  ∀ k p, p.grade ≠ nu → x (k, p) = 0

/-- An exact-grade projected vector is supported at that grade.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem gradeProjection_supported (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    SupportedAtGrade nu
      (Matrix.mulVec (gradeProjection (d := d) nu) x) := by
  intro k p hp
  rw [gradeProjection_mulVec]
  simp [hp]

/-- A grade-supported vector has zero external fiber outside its grade.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem fiber_eq_zero_of_not_grade {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x)
    {p : Pattern m n} (hp : p.grade ≠ nu) :
    fiber x p = 0 := by
  ext k
  exact hx k p hp

/-- A grade-supported vector has zero frame contraction outside its grade.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem contract_eq_zero_of_not_grade {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x)
    (F : Frame n d) (c : Fin n) {p : Pattern m n}
    (hp : p.grade ≠ nu) :
    contract F c x p = 0 := by
  rw [contract_eq_analyze, fiber_eq_zero_of_not_grade hx hp]
  simp [analyze]

/-- A sum of all ordered realizations of one word has the word's exact grade
shift.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem physicalWordSum_homogeneous (u : Fin n → Fin d → ℝ) (w : Word) :
    ExternalOperator.Homogeneous w.degree (physicalWordSum m u w) := by
  intro out inp hnonzero
  classical
  simp only [physicalWordSum, Matrix.sum_apply] at hnonzero
  by_contra hgrade
  apply hnonzero
  apply Finset.sum_eq_zero
  intro r _
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  by_contra hterm
  exact hgrade
    (orderedWordTerm_homogeneous u r
      (Ne.symm (Finset.mem_erase.mp hj).1) w hterm)

/-- The directional mixed raising band has grade shift two.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yplus_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 2 (Yplus m (frameRows F)) := by
  simpa [Yplus, wordSum, Word.degree, Leg.degree] using
    physicalWordSum_homogeneous (m := m) (frameRows F) (.rUp, .pUp)

/-- The directional mixed preserving band has grade shift zero.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yzero_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 0 (Yzero m (frameRows F)) := by
  simpa [Yzero, wordSum, Word.degree, Leg.degree] using
    physicalWordSum_homogeneous (m := m) (frameRows F) (.rDown, .pUp)

/-- The heavy correction band has grade shift zero.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hprime_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 0 (Hprime m (frameRows F)) := by
  simpa [Hprime, wordSum, Word.degree, Leg.degree] using
    physicalWordSum_homogeneous (m := m) (frameRows F) (.pDown, .pUp)

/-- Homogeneity plus exact input support makes every incompatible output fiber
identically zero.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem fullFiber_mulVec_eq_zero_of_grade {delta : ℤ}
    {A : FullOp d m n} (hA : ExternalOperator.Homogeneous delta A)
    {nu : ℕ} {x : Fin d × Pattern m n → ℝ}
    (hx : SupportedAtGrade nu x) (p : Pattern m n)
    (hp : (p.grade : ℤ) ≠ (nu : ℤ) + delta) :
    fullFiber (Matrix.mulVec A x) p = 0 := by
  ext k
  simp only [fullFiber, PiLp.toLp_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro inp _
  by_cases hin : inp.2.grade = nu
  · by_cases hentry : A (k, p) inp = 0
    · simp [hentry]
    · have hrel := homogeneous_grade_relation hA hentry
      exfalso
      apply hp
      simpa [hin] using hrel
  · simp [hx inp.1 inp.2 hin]

/-- Coefficient energy indexed by actual finite marked patterns.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def markedEnergy (a b : Level) (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) : ℝ :=
  ∑ z : RowMark m n a b, (contract F z.right x z.pattern) ^ 2

/-- Marked-pair energy equals the literal nested sum over patterns, rows, and admissible sites.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem markedEnergy_eq_nested (a b : Level) (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    markedEnergy a b F x =
      ∑ p, ∑ r, ∑ i ∈ levelInRow p r a,
        ∑ j ∈ (levelInRow p r b).erase i,
          (contract F j x p) ^ 2 := by
  exact sum_rowMark_eq_nested a b
    (fun p _ _ j ↦ (contract F j x p) ^ 2)

/-- For a fixed input pattern, fresh-site Parseval is paid once per marked
light site.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem light_fresh_energy_at_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    (∑ r, ∑ a ∈ p.lightInRow r,
      ∑ c ∈ p.freshInRow r |>.erase a,
        (contract F c x p) ^ 2) ≤
      (p.light.card : ℝ) * ParsevalFrame.normSq (fiber x p) := by
  calc
    (∑ r, ∑ a ∈ p.lightInRow r,
        ∑ c ∈ p.freshInRow r |>.erase a,
          (contract F c x p) ^ 2) ≤
        ∑ r, ∑ a ∈ p.lightInRow r,
          ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro a _
      simpa only [contract_eq_analyze] using
        subset_analysis F ((p.freshInRow r).erase a) (fiber x p)
    _ = (p.light.card : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.sum_mul]
      norm_cast
      rw [← Pattern.card_light_eq_sum_card_lightInRow]

/-- For a fixed input pattern, fresh-site Parseval is paid once per marked
heavy site.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem heavy_fresh_energy_at_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    (∑ r, ∑ a ∈ p.heavyInRow r,
      ∑ c ∈ p.freshInRow r |>.erase a,
        (contract F c x p) ^ 2) ≤
      (p.heavy.card : ℝ) * ParsevalFrame.normSq (fiber x p) := by
  calc
    (∑ r, ∑ a ∈ p.heavyInRow r,
        ∑ c ∈ p.freshInRow r |>.erase a,
          (contract F c x p) ^ 2) ≤
        ∑ r, ∑ a ∈ p.heavyInRow r,
          ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro a _
      simpa only [contract_eq_analyze] using
        subset_analysis F ((p.freshInRow r).erase a) (fiber x p)
    _ = (p.heavy.card : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.sum_mul]
      norm_cast
      rw [← Pattern.card_heavy_eq_sum_card_heavyInRow]

/-- Fully concrete input-side resummation for light marks.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem markedEnergy_one_zero_le (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    markedEnergy .one .zero F x ≤
      (nu : ℝ) * FiniteHilbert.normSq x := by
  rw [markedEnergy_eq_nested]
  simp only [levelInRow_one, levelInRow_zero]
  calc
    (∑ p, ∑ r, ∑ i ∈ p.lightInRow r,
        ∑ j ∈ (p.freshInRow r).erase i,
          contract F j x p ^ 2) ≤
        ∑ p, (nu : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p.grade = nu
      · calc
          (∑ r, ∑ i ∈ p.lightInRow r,
              ∑ j ∈ (p.freshInRow r).erase i,
                contract F j x p ^ 2) ≤
              (p.light.card : ℝ) * ParsevalFrame.normSq (fiber x p) :=
                light_fresh_energy_at_le F x p
          _ ≤ (nu : ℝ) * ParsevalFrame.normSq (fiber x p) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast (hp ▸ p.card_light_le_grade)
            · exact real_inner_self_nonneg
      · have hfiber : fiber x p = 0 := fiber_eq_zero_of_not_grade hx hp
        calc
          (∑ r, ∑ i ∈ p.lightInRow r,
              ∑ j ∈ (p.freshInRow r).erase i,
                contract F j x p ^ 2) ≤
              (p.light.card : ℝ) * ParsevalFrame.normSq (fiber x p) :=
                light_fresh_energy_at_le F x p
          _ = 0 := by simp [hfiber, ParsevalFrame.normSq]
          _ = (nu : ℝ) * ParsevalFrame.normSq (fiber x p) := by
            simp [hfiber, ParsevalFrame.normSq]
    _ = (nu : ℝ) * FiniteHilbert.normSq x := by
      rw [← Finset.mul_sum]
      congr 1
      simpa [fiber, fullFiber] using (full_normSq_eq_sum_fiber x).symm

/-- Fully concrete input-side resummation for heavy marks, with the factor two
kept denominator-free.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem two_mul_markedEnergy_two_zero_le (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    2 * markedEnergy .two .zero F x ≤
      (nu : ℝ) * FiniteHilbert.normSq x := by
  rw [markedEnergy_eq_nested]
  simp only [levelInRow_two, levelInRow_zero]
  calc
    2 * (∑ p, ∑ r, ∑ i ∈ p.heavyInRow r,
        ∑ j ∈ (p.freshInRow r).erase i,
          contract F j x p ^ 2) =
        ∑ p, 2 * (∑ r, ∑ i ∈ p.heavyInRow r,
          ∑ j ∈ (p.freshInRow r).erase i,
            contract F j x p ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ p, (nu : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p.grade = nu
      · have hlocal := heavy_fresh_energy_at_le F x p
        have hcountNat : 2 * p.heavy.card ≤ nu := by
          simpa [hp] using p.two_mul_card_heavy_le_grade
        have hcount : (2 : ℝ) * (p.heavy.card : ℝ) ≤ (nu : ℝ) := by
          exact_mod_cast hcountNat
        calc
          2 * (∑ r, ∑ i ∈ p.heavyInRow r,
              ∑ j ∈ (p.freshInRow r).erase i,
                contract F j x p ^ 2) ≤
              2 * ((p.heavy.card : ℝ) *
                ParsevalFrame.normSq (fiber x p)) := by linarith
          _ = ((2 : ℝ) * (p.heavy.card : ℝ)) *
                ParsevalFrame.normSq (fiber x p) := by ring
          _ ≤ (nu : ℝ) * ParsevalFrame.normSq (fiber x p) := by
            exact mul_le_mul_of_nonneg_right hcount real_inner_self_nonneg
      · have hfiber : fiber x p = 0 := fiber_eq_zero_of_not_grade hx hp
        have hlocal := heavy_fresh_energy_at_le F x p
        calc
          2 * (∑ r, ∑ i ∈ p.heavyInRow r,
              ∑ j ∈ (p.freshInRow r).erase i,
                contract F j x p ^ 2) ≤
              2 * ((p.heavy.card : ℝ) *
                ParsevalFrame.normSq (fiber x p)) := by linarith
          _ = 0 := by simp [hfiber, ParsevalFrame.normSq]
          _ = (nu : ℝ) * ParsevalFrame.normSq (fiber x p) := by
            simp [hfiber, ParsevalFrame.normSq]
    _ = (nu : ℝ) * FiniteHilbert.normSq x := by
      rw [← Finset.mul_sum]
      congr 1
      simpa [fiber, fullFiber] using (full_normSq_eq_sum_fiber x).symm

end

end DirectionalConcrete

end NLAlib.SparseFock
