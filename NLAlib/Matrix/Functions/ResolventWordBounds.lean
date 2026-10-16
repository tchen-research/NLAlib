import NLAlib.Matrix.Functions.ResolventDifferences
import NLAlib.Matrix.Norms.SchattenWords

/-!
# Sharp bounds for the ordered resolvent remainder

Each ordered second difference contains exactly three words, each with
four resolvents and three Schatten-three directions after pairing with
a trace direction. No independence is used in these deterministic bounds.
Source: supplied Cauchy-transform reroute, six-word remainder estimate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- The ordered second squared-resolvent difference has the exact three-word
trace bound with four powers of the nonreal-shift denominator.
Source: supplied Cauchy-transform reroute (comparison-sixwords).
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem norm_normalizedTrace_mul_resolventSquareSecondDifference_le
    (ζ : ℂ) (A B C D H K : M) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hC : C.IsHermitian) (hζ : ζ.im ≠ 0) :
    ‖normalizedTrace (D * resolventSquareSecondDifference ζ A B C H K)‖ ≤
      3 * |ζ.im|⁻¹^4 * schattenNormReal D 3 * schattenNormReal H 3 *
        schattenNormReal K 3 / (Fintype.card n : ℝ) := by
  let RA := resolvent A ζ
  let RB := resolvent B ζ
  let RC := resolvent C ζ
  let c := |ζ.im|⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr (abs_nonneg _)
  have hRA : specNorm RA ≤ c := hA.specNorm_resolvent_le hζ
  have hRB : specNorm RB ≤ c := hB.specNorm_resolvent_le hζ
  have hRC : specNorm RC ≤ c := hC.specNorm_resolvent_le hζ
  let b := c^4 * schattenNormReal D 3 * schattenNormReal H 3 *
    schattenNormReal K 3 / (Fintype.card n : ℝ)
  have h₁ : ‖normalizedTrace (D*RA^2*H*RB*K*RC)‖ ≤ b := by
    simpa only [pow_two,Matrix.mul_assoc] using
      norm_normalizedTrace_word_pair_le_schattenNormReal_three_mul D RA RA H RB K RC
        hc hRA hRA hRB hRC
  have h₂ : ‖normalizedTrace (D*RA*H*RB^2*K*RC)‖ ≤ b := by
    have he : normalizedTrace (D*RA*H*RB^2*K*RC) =
        normalizedTrace (H*RB*RB*K*RC*D*RA) := by
      calc
        _ = normalizedTrace ((D*RA)*(H*RB^2*K*RC)) := congrArg normalizedTrace (by noncomm_ring)
        _ = normalizedTrace ((H*RB^2*K*RC)*(D*RA)) := normalizedTrace_mul_comm _ _
        _ = _ := congrArg normalizedTrace (by noncomm_ring)
    calc
      _ = ‖normalizedTrace (H*RB*RB*K*RC*D*RA)‖ := congrArg norm he
      _ ≤ (c^4 * schattenNormReal H 3 * schattenNormReal K 3 * schattenNormReal D 3) /
          (Fintype.card n : ℝ) :=
        norm_normalizedTrace_word_pair_le_schattenNormReal_three_mul H RB RB K RC D RA
          hc hRB hRB hRC hRA
      _ = b := by dsimp [b]; ring
  have h₃ : ‖normalizedTrace (D*RA*H*RB*K*RC^2)‖ ≤ b := by
    have he : normalizedTrace (D*RA*H*RB*K*RC^2) =
        normalizedTrace (K*RC*RC*D*RA*H*RB) := by
      calc
        _ = normalizedTrace ((D*RA*H*RB)*(K*RC^2)) := congrArg normalizedTrace (by noncomm_ring)
        _ = normalizedTrace ((K*RC^2)*(D*RA*H*RB)) := normalizedTrace_mul_comm _ _
        _ = _ := congrArg normalizedTrace (by noncomm_ring)
    calc
      _ = ‖normalizedTrace (K*RC*RC*D*RA*H*RB)‖ := congrArg norm he
      _ ≤ (c^4 * schattenNormReal K 3 * schattenNormReal D 3 * schattenNormReal H 3) /
          (Fintype.card n : ℝ) :=
        norm_normalizedTrace_word_pair_le_schattenNormReal_three_mul K RC RC D RA H RB
          hc hRC hRC hRA hRB
      _ = b := by dsimp [b]; ring
  have hs : normalizedTrace (D * resolventSquareSecondDifference ζ A B C H K) =
      normalizedTrace (D*RA^2*H*RB*K*RC) + normalizedTrace (D*RA*H*RB^2*K*RC) +
        normalizedTrace (D*RA*H*RB*K*RC^2) := by
    have hm : D * resolventSquareSecondDifference ζ A B C H K =
        D*RA^2*H*RB*K*RC + D*RA*H*RB^2*K*RC + D*RA*H*RB*K*RC^2 := by
      dsimp [resolventSquareSecondDifference,RA,RB,RC]
      noncomm_ring
    rw [hm,normalizedTrace_add,normalizedTrace_add]
  rw [hs]
  calc
    _ ≤ ‖normalizedTrace (D*RA^2*H*RB*K*RC)‖ +
        ‖normalizedTrace (D*RA*H*RB^2*K*RC)‖ + ‖normalizedTrace (D*RA*H*RB*K*RC^2)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ b+b+b := add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by dsimp [b,c]; ring

end NLAlib
