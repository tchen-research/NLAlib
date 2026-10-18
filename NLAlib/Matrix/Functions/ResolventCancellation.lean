import NLAlib.Matrix.Functions.AggregateResolvent
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Exact cubic remainder for resolvent derivatives

Three-slot telescoping restores the same reference resolvent in both
first-difference words. The resulting six ordered cubic words are actual
matrices and require no Taylor-remainder or norm-bound hypothesis.

Source: Tatiana Brailovskaya and Ramon van Handel, *Universality and sharp
matrix concentration inequalities*, arXiv:2201.05142v3 (2024), §6.4, proof
of Lemma 6.11. This supports `matrix-resolvent-gaussian-universality`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib

private theorem three_slot_telescope {𝔸 : Type*} [Ring 𝔸]
    (A B C H U V : 𝔸) :
    A * U * B * V * C - H * U * H * V * H =
      (A - H) * U * B * V * C + H * U * (B - H) * V * C +
        H * U * H * V * (C - H) := by
  noncomm_ring

private theorem mul_sub_mul_eq_smul_add_smul_sq
    {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸]
    (R₀ R₁ R₂ D E F : 𝔸) (a : ℝ)
    (h₀₁ : R₀ - R₁ = a • (R₀ * D * R₁))
    (h₀₂ : R₀ - R₂ = a • (R₀ * F * R₂))
    (h₁₂ : R₁ - R₂ = a • (R₁ * E * R₂)) :
    R₀ * D * R₀ - R₁ * D * R₁ =
      a • ((2 : ℝ) • (R₂ * D * R₂ * D * R₂)) +
        a ^ 2 •
          (R₀ * F * R₂ * D * R₁ * D * R₀ +
            R₂ * D * R₁ * E * R₂ * D * R₀ +
            R₂ * D * R₂ * D * R₀ * F * R₂ +
            R₁ * E * R₂ * D * R₀ * D * R₁ +
            R₂ * D * R₀ * F * R₂ * D * R₁ +
            R₂ * D * R₂ * D * R₁ * E * R₂) := by
  let T := R₂ * D * R₂ * D * R₂
  let X := R₀ * F * R₂ * D * R₁ * D * R₀ +
    R₂ * D * R₁ * E * R₂ * D * R₀ +
    R₂ * D * R₂ * D * R₀ * F * R₂
  let Y := R₁ * E * R₂ * D * R₀ * D * R₁ +
    R₂ * D * R₀ * F * R₂ * D * R₁ +
    R₂ * D * R₂ * D * R₁ * E * R₂
  have hfirst : R₀ * D * R₀ - R₁ * D * R₁ =
      a • (R₀ * D * R₁ * D * R₀ + R₁ * D * R₀ * D * R₁) := by
    calc
      _ = (R₀ - R₁) * D * R₀ + R₁ * D * (R₀ - R₁) := by noncomm_ring
      _ = _ := by
        rw [h₀₁]
        simp only [smul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]
  have hleft : R₀ * D * R₁ * D * R₀ - T = a • X := by
    dsimp only [T, X]
    calc
      _ = (R₀ - R₂) * D * R₁ * D * R₀ + R₂ * D * (R₁ - R₂) * D * R₀ +
          R₂ * D * R₂ * D * (R₀ - R₂) := three_slot_telescope R₀ R₁ R₀ R₂ D D
      _ = _ := by
        rw [h₀₂, h₁₂]
        simp only [smul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]
  have hright : R₁ * D * R₀ * D * R₁ - T = a • Y := by
    dsimp only [T, Y]
    calc
      _ = (R₁ - R₂) * D * R₀ * D * R₁ + R₂ * D * (R₀ - R₂) * D * R₁ +
          R₂ * D * R₂ * D * (R₁ - R₂) := three_slot_telescope R₁ R₀ R₁ R₂ D D
      _ = _ := by
        rw [h₁₂, h₀₂]
        simp only [smul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]
  have ht : R₀ * D * R₁ * D * R₀ + R₁ * D * R₀ * D * R₁ =
      (2 : ℝ) • T + a • (X + Y) := by
    rw [sub_eq_iff_eq_add'.mp hleft, sub_eq_iff_eq_add'.mp hright]
    simp only [two_smul, smul_add]
    abel
  have hsum : X + Y =
      R₀ * F * R₂ * D * R₁ * D * R₀ +
        R₂ * D * R₁ * E * R₂ * D * R₀ +
        R₂ * D * R₂ * D * R₀ * F * R₂ +
        R₁ * E * R₂ * D * R₀ * D * R₁ +
        R₂ * D * R₀ * F * R₂ * D * R₁ +
        R₂ * D * R₂ * D * R₁ * E * R₂ := by dsimp [X, Y]; abel
  calc
    _ = a • (R₀ * D * R₁ * D * R₀ + R₁ * D * R₀ * D * R₁) := hfirst
    _ = a • ((2 : ℝ) • T + a • (X + Y)) := congrArg (fun q : 𝔸 => a • q) ht
    _ = a • ((2 : ℝ) • T) + a • (a • (X + Y)) := smul_add a _ _
    _ = a • ((2 : ℝ) • T) + a ^ 2 • (X + Y) := by
      rw [smul_smul a a (X + Y), pow_two]
    _ = _ := by
      simpa only [T] using
        congrArg (fun q : 𝔸 => a • ((2 : ℝ) • T) + a ^ 2 • q) hsum

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ


/-- The six ordered cubic resolvent words obtained by comparing two directional
resolvent derivatives at the common third base. The three bases are `A₀`,
`A₀ - a • D` and `A₀ - a • F`, with the third direction `F - D`.
The definition is total; Hermiticity and a nonreal shift are hypotheses of
its cancellation and norm theorems.
Source: Brailovskaya--van Handel, arXiv:2201.05142v3 (2024), §6.4,
proof of Lemma 6.11. -/
def resolventCubicRemainder (A₀ D F : M) (a : ℝ) (ζ : ℂ) : M :=
  let R₀ := resolvent A₀ ζ
  let R₁ := resolvent (A₀ - a • D) ζ
  let R₂ := resolvent (A₀ - a • F) ζ
  let E := F - D
  R₀ * F * R₂ * D * R₁ * D * R₀ +
    R₂ * D * R₁ * E * R₂ * D * R₀ +
    R₂ * D * R₂ * D * R₀ * F * R₂ +
    R₁ * E * R₂ * D * R₀ * D * R₁ +
    R₂ * D * R₀ * F * R₂ * D * R₁ +
    R₂ * D * R₂ * D * R₁ * E * R₂

/-- Two directional resolvent derivatives differ by the common quadratic
term and six explicit cubic words. Every factor is the actual resolvent of a
Hermitian matrix, and the real interpolation coefficient is arbitrary.

Source: Tatiana Brailovskaya and Ramon van Handel, *Universality and sharp
matrix concentration inequalities*, arXiv:2201.05142v3 (2024), §6.4, proof
of Lemma 6.11, with the exact ordered remainder made explicit.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem resolvent_mul_resolvent_sub_eq_smul_add_smul_sq
    (A₀ D F : M) (a : ℝ) (ζ : ℂ) (hA₀ : A₀.IsHermitian)
    (hD : D.IsHermitian) (hF : F.IsHermitian) (hζ : ζ.im ≠ 0) :
    let R₀ := resolvent A₀ ζ
    let R₁ := resolvent (A₀ - a • D) ζ
    let R₂ := resolvent (A₀ - a • F) ζ
    R₀ * D * R₀ - R₁ * D * R₁ =
      a • ((2 : ℝ) • (R₂ * D * R₂ * D * R₂)) +
        a ^ 2 • resolventCubicRemainder A₀ D F a ζ := by
  dsimp only
  have h₀₁ : resolvent A₀ ζ - resolvent (A₀ - a • D) ζ =
      a • (resolvent A₀ ζ * D * resolvent (A₀ - a • D) ζ) := by
    have h := resolvent_sub_smul_eq_sub_mul_resolvent A₀ D a ζ hA₀ hD hζ
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using (eq_sub_iff_add_eq.mp h).symm
  have h₀₂ : resolvent A₀ ζ - resolvent (A₀ - a • F) ζ =
      a • (resolvent A₀ ζ * F * resolvent (A₀ - a • F) ζ) := by
    have h := resolvent_sub_smul_eq_sub_mul_resolvent A₀ F a ζ hA₀ hF hζ
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using (eq_sub_iff_add_eq.mp h).symm
  have hbase : (A₀ - a • D) - a • (F - D) = A₀ - a • F := by
    simp only [smul_sub]
    abel
  have h₁₂ : resolvent (A₀ - a • D) ζ - resolvent (A₀ - a • F) ζ =
      a • (resolvent (A₀ - a • D) ζ * (F - D) * resolvent (A₀ - a • F) ζ) := by
    have h := resolvent_sub_smul_eq_sub_mul_resolvent (A₀ - a • D) (F - D) a ζ
      (hA₀.sub (hD.smul (isSelfAdjoint_iff.mpr (star_trivial a)))) (hF.sub hD) hζ
    rw [hbase] at h
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using (eq_sub_iff_add_eq.mp h).symm
  exact mul_sub_mul_eq_smul_add_smul_sq _ _ _ D (F - D) F a h₀₁ h₀₂ h₁₂


variable {ι : Type*} [Fintype ι]

private theorem specNorm_sum_resolvent_seven_factors_le
    (A : M) (Z T U V W H K : ι → M) (α β r : ℝ) (ζ : ℂ)
    (hA : A.IsHermitian) (hZ : ∀ i, (Z i).IsHermitian)
    (hT : ∀ i, (T i).IsHermitian) (hU : ∀ i, (U i).IsHermitian)
    (hW : ∀ i, (W i).IsHermitian) (hr : 0 ≤ r)
    (hUnorm : ∀ i, specNorm (U i) ≤ r) (hVnorm : ∀ i, specNorm (V i) ≤ r)
    (hWnorm : ∀ i, specNorm (W i) ≤ r)
    (hH : ∀ i, specNorm (H i) ≤ |ζ.im|⁻¹)
    (hK : ∀ i, specNorm (K i) ≤ |ζ.im|⁻¹) (hζ : ζ.im ≠ 0) :
    specNorm (∑ i, resolvent (A - α • Z i) ζ * U i * H i * V i * K i * W i *
      resolvent (A - β • T i) ζ) ≤
      r * |ζ.im|⁻¹ ^ 4 * (specNorm (∑ i, U i ^ 2) + specNorm (∑ i, W i ^ 2)) +
        r ^ 3 * |ζ.im|⁻¹ ^ 6 *
          (α ^ 2 * specNorm (∑ i, Z i ^ 2) + β ^ 2 * specNorm (∑ i, T i ^ 2)) := by
  have hc : 0 ≤ |ζ.im|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
  have hmid : ∀ i, specNorm (H i * V i * K i) ≤ r * |ζ.im|⁻¹ ^ 2 := by
    intro i
    calc
      _ ≤ (specNorm (H i) * specNorm (V i)) * specNorm (K i) :=
        (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (specNorm_mul_le _ _) (specNorm_nonneg _))
      _ ≤ (|ζ.im|⁻¹ * r) * |ζ.im|⁻¹ :=
        mul_le_mul (mul_le_mul (hH i) (hVnorm i) (specNorm_nonneg _) hc)
          (hK i) (specNorm_nonneg _) (mul_nonneg hc hr)
      _ = _ := by ring
  have h := specNorm_sum_resolvent_mul_mul_resolvent_le A Z T U
    (fun i => H i * V i * K i) W α β r (r * |ζ.im|⁻¹ ^ 2) ζ
    hA hZ hT hU hW hr (by positivity) hUnorm hmid hWnorm hζ
  have h' : specNorm (∑ i, resolvent (A - α • Z i) ζ * U i * H i * V i * K i * W i *
      resolvent (A - β • T i) ζ) ≤
      (r * |ζ.im|⁻¹ ^ 2) * |ζ.im|⁻¹ ^ 2 *
        (specNorm (∑ i, U i ^ 2) + specNorm (∑ i, W i ^ 2)) +
      (r * |ζ.im|⁻¹ ^ 2) * r ^ 2 * |ζ.im|⁻¹ ^ 4 *
        (α ^ 2 * specNorm (∑ i, Z i ^ 2) + β ^ 2 * specNorm (∑ i, T i ^ 2)) := by
    simpa only [Matrix.mul_assoc] using h
  exact h'.trans_eq (by ring)

/-- The actual six-word cubic remainder retains the aggregate squared
sizes of all three directions. Its explicit coefficients count the two
endpoint contributions and the actual endpoint perturbations of each word.
No independence, smallness or bound on a sum of individual cubic norms is used.

Source: Tatiana Brailovskaya and Ramon van Handel, *Universality and sharp
matrix concentration inequalities*, arXiv:2201.05142v3 (2024), §6.4, proof
of Lemma 6.11, with the six ordered words and constants made explicit.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem specNorm_sum_resolventCubicRemainder_le
    (A : M) (D F : ι → M) (a r : ℝ) (ζ : ℂ)
    (hA : A.IsHermitian) (hD : ∀ i, (D i).IsHermitian)
    (hF : ∀ i, (F i).IsHermitian) (hr : 0 ≤ r)
    (hDnorm : ∀ i, specNorm (D i) ≤ r) (hFnorm : ∀ i, specNorm (F i) ≤ r)
    (hEnorm : ∀ i, specNorm (F i - D i) ≤ r) (hζ : ζ.im ≠ 0) :
    specNorm (∑ i, resolventCubicRemainder A (D i) (F i) a ζ) ≤
      r * |ζ.im|⁻¹ ^ 4 *
        (8 * specNorm (∑ i, D i ^ 2) + 2 * specNorm (∑ i, (F i - D i) ^ 2) +
          2 * specNorm (∑ i, F i ^ 2)) +
        a ^ 2 * r ^ 3 * |ζ.im|⁻¹ ^ 6 *
          (3 * specNorm (∑ i, D i ^ 2) + 6 * specNorm (∑ i, F i ^ 2)) := by
  let E : ι → M := fun i => F i - D i
  let R₀ : ι → M := fun _ => resolvent A ζ
  let R₁ : ι → M := fun i => resolvent (A - a • D i) ζ
  let R₂ : ι → M := fun i => resolvent (A - a • F i) ζ
  let w₁ : ι → M := fun i => R₀ i * F i * R₂ i * D i * R₁ i * D i * R₀ i
  let w₂ : ι → M := fun i => R₂ i * D i * R₁ i * E i * R₂ i * D i * R₀ i
  let w₃ : ι → M := fun i => R₂ i * D i * R₂ i * D i * R₀ i * F i * R₂ i
  let w₄ : ι → M := fun i => R₁ i * E i * R₂ i * D i * R₀ i * D i * R₁ i
  let w₅ : ι → M := fun i => R₂ i * D i * R₀ i * F i * R₂ i * D i * R₁ i
  let w₆ : ι → M := fun i => R₂ i * D i * R₂ i * D i * R₁ i * E i * R₂ i
  have hE (i : ι) : (E i).IsHermitian := (hF i).sub (hD i)
  have hR₀ (i : ι) : specNorm (R₀ i) ≤ |ζ.im|⁻¹ := hA.specNorm_resolvent_le hζ
  have hR₁ (i : ι) : specNorm (R₁ i) ≤ |ζ.im|⁻¹ :=
    (hA.sub ((hD i).smul (isSelfAdjoint_iff.mpr (star_trivial a)))).specNorm_resolvent_le hζ
  have hR₂ (i : ι) : specNorm (R₂ i) ≤ |ζ.im|⁻¹ :=
    (hA.sub ((hF i).smul (isSelfAdjoint_iff.mpr (star_trivial a)))).specNorm_resolvent_le hζ
  have h₁ := specNorm_sum_resolvent_seven_factors_le A (fun _ : ι => 0) (fun _ : ι => 0)
    F D D R₂ R₁ 0 0 r ζ hA (fun _ => Matrix.isHermitian_zero)
    (fun _ => Matrix.isHermitian_zero) hF hD hr hFnorm hDnorm hDnorm hR₂ hR₁ hζ
  have h₂ := specNorm_sum_resolvent_seven_factors_le A F (fun _ : ι => 0)
    D E D R₁ R₂ a 0 r ζ hA hF (fun _ => Matrix.isHermitian_zero)
    hD hD hr hDnorm hEnorm hDnorm hR₁ hR₂ hζ
  have h₃ := specNorm_sum_resolvent_seven_factors_le A F F
    D D F R₂ R₀ a a r ζ hA hF hF hD hF hr hDnorm hDnorm hFnorm hR₂ hR₀ hζ
  have h₄ := specNorm_sum_resolvent_seven_factors_le A D D
    E D D R₂ R₀ a a r ζ hA hD hD hE hD hr hEnorm hDnorm hDnorm hR₂ hR₀ hζ
  have h₅ := specNorm_sum_resolvent_seven_factors_le A F D
    D F D R₀ R₂ a a r ζ hA hF hD hD hD hr hDnorm hFnorm hDnorm hR₀ hR₂ hζ
  have h₆ := specNorm_sum_resolvent_seven_factors_le A F F
    D D E R₂ R₁ a a r ζ hA hF hF hD hE hr hDnorm hDnorm hEnorm hR₂ hR₁ hζ
  simp only [zero_smul, sub_zero] at h₁ h₂
  change specNorm (∑ i, w₁ i) ≤ _ at h₁
  change specNorm (∑ i, w₂ i) ≤ _ at h₂
  change specNorm (∑ i, w₃ i) ≤ _ at h₃
  change specNorm (∑ i, w₄ i) ≤ _ at h₄
  change specNorm (∑ i, w₅ i) ≤ _ at h₅
  change specNorm (∑ i, w₆ i) ≤ _ at h₆
  have hsum : (∑ i, resolventCubicRemainder A (D i) (F i) a ζ) =
      (∑ i, w₁ i) + (∑ i, w₂ i) + (∑ i, w₃ i) +
        (∑ i, w₄ i) + (∑ i, w₅ i) + (∑ i, w₆ i) := by
    change (∑ i, (w₁ i + w₂ i + w₃ i + w₄ i + w₅ i + w₆ i)) = _
    simp only [Finset.sum_add_distrib]
  have htri : specNorm ((∑ i, w₁ i) + (∑ i, w₂ i) + (∑ i, w₃ i) +
        (∑ i, w₄ i) + (∑ i, w₅ i) + (∑ i, w₆ i)) ≤
      specNorm (∑ i, w₁ i) + specNorm (∑ i, w₂ i) + specNorm (∑ i, w₃ i) +
        specNorm (∑ i, w₄ i) + specNorm (∑ i, w₅ i) + specNorm (∑ i, w₆ i) := by
    have ht₂ := specNorm_add_le (∑ i, w₁ i) (∑ i, w₂ i)
    have ht₃ := specNorm_add_le ((∑ i, w₁ i) + (∑ i, w₂ i)) (∑ i, w₃ i)
    have ht₄ := specNorm_add_le ((∑ i, w₁ i) + (∑ i, w₂ i) + (∑ i, w₃ i)) (∑ i, w₄ i)
    have ht₅ := specNorm_add_le ((∑ i, w₁ i) + (∑ i, w₂ i) + (∑ i, w₃ i) +
      (∑ i, w₄ i)) (∑ i, w₅ i)
    have ht₆ := specNorm_add_le ((∑ i, w₁ i) + (∑ i, w₂ i) + (∑ i, w₃ i) +
      (∑ i, w₄ i) + (∑ i, w₅ i)) (∑ i, w₆ i)
    linarith only [ht₂, ht₃, ht₄, ht₅, ht₆]
  have hbound := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄) h₅) h₆
  rw [hsum]
  exact htri.trans (hbound.trans_eq (by dsimp only [E]; ring))

end NLAlib
