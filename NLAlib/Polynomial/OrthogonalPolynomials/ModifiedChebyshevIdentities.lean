import NLAlib.Polynomial.OrthogonalPolynomials.Recurrence
import NLAlib.Polynomial.OrthogonalPolynomials.PositiveMomentFunctional

/-!
# Mixed moments for the modified Chebyshev algorithm

The finite mixed table pairs the canonical monic orthogonal polynomials with a
given monic reference family. Its triangularity, diagonal norms and recurrence
give the coefficients used by Gautschi's modified Chebyshev algorithm. Only the
displayed finite Hankel systems need be nonsingular.
Source: Gautschi (2004), Algorithm 2.1.
-/

noncomputable section
open Polynomial
namespace NLAlib

/-- Mixed moment of the canonical monic polynomial and a reference polynomial.
Only the product's moment is used; no infinite orthogonal expansion is involved. -/
def orthogonalMixedMoment (L : ℝ[X] →ₗ[ℝ] ℝ) (p : ℕ → ℝ[X]) (k l : ℕ) : ℝ :=
  L (monicOrthogonalPolynomial L k * p l)

/-- Row zero of the mixed table is exactly the supplied modified moments. -/
@[simp] theorem orthogonalMixedMoment_zero (L : ℝ[X] →ₗ[ℝ] ℝ) (p : ℕ → ℝ[X]) (l : ℕ) :
    orthogonalMixedMoment L p 0 l = L (p l) := by
  simp [orthogonalMixedMoment]

/-- The mixed table vanishes below its diagonal. -/
theorem orthogonalMixedMoment_eq_zero {L : ℝ[X] →ₗ[ℝ] ℝ} {p : ℕ → ℝ[X]}
    {k l : ℕ} (hL : hankelMomentDet L k ≠ 0) (hp : (p l).degree = l) (hl : l < k) :
    orthogonalMixedMoment L p k l = 0 := by
  apply (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L hL).orthogonal
  rw [hp]
  exact_mod_cast hl

/-- Monicity makes each diagonal mixed moment the canonical squared norm. -/
theorem orthogonalMixedMoment_diag {L : ℝ[X] →ₗ[ℝ] ℝ} {p : ℕ → ℝ[X]} {k : ℕ}
    (hL : hankelMomentDet L k ≠ 0) (hp : (p k).Monic) (hdeg : (p k).natDegree = k) :
    orthogonalMixedMoment L p k k = orthogonalPolynomialNorm L k :=
  (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L hL).functional_mul_eq_sq_of_monic
    hp hdeg

/-- The mixed table obeys the finite modified Chebyshev recurrence. At column
zero the previous reference polynomial is absent; the native orthogonal `beta`
is zero at row zero.
atlas: modified-chebyshev-algorithm (partial) -/
theorem orthogonalMixedMoment_succ (L : ℝ[X] →ₗ[ℝ] ℝ) (p : ℕ → ℝ[X])
    (a b : ℕ → ℝ) (k l : ℕ)
    (hL : ∀ j ≤ k + 1, hankelMomentDet L j ≠ 0)
    (hp : X * p l = p (l + 1) + C (a l) * p l +
      if l = 0 then 0 else C (b l) * p (l - 1)) :
    orthogonalMixedMoment L p (k + 1) l = orthogonalMixedMoment L p k (l + 1) +
      (a l - orthogonalRecurrenceAlpha L k) * orthogonalMixedMoment L p k l -
      orthogonalRecurrenceBeta L k * orthogonalMixedMoment L p (k - 1) l +
      if l = 0 then 0 else b l * orthogonalMixedMoment L p k (l - 1) := by
  unfold orthogonalMixedMoment
  rw [monicOrthogonalPolynomial_succ_eq L k hL]
  have he : ((X - C (orthogonalRecurrenceAlpha L k)) * monicOrthogonalPolynomial L k -
      C (orthogonalRecurrenceBeta L k) * monicOrthogonalPolynomial L (k - 1)) * p l =
      monicOrthogonalPolynomial L k * (X * p l) -
        C (orthogonalRecurrenceAlpha L k) * (monicOrthogonalPolynomial L k * p l) -
        C (orthogonalRecurrenceBeta L k) * (monicOrthogonalPolynomial L (k - 1) * p l) := by ring
  rw [he, hp]
  split_ifs <;>
    simp only [mul_add, add_zero, map_add, map_sub, C_mul', mul_smul_comm,
      map_smul, smul_eq_mul] <;> ring

/-- Positive finite moment data make the mixed table's included diagonal entries
positive, so the algorithm's divisions are justified by the input data. -/
theorem orthogonalMixedMoment_diag_pos {L : ℝ[X] →ₗ[ℝ] ℝ} {p : ℕ → ℝ[X]} {n k : ℕ}
    (hL : (hankelMomentMatrix L n).PosDef) (hk : k < n)
    (hp : (p k).Monic) (hdeg : (p k).natDegree = k) :
    0 < orthogonalMixedMoment L p k k := by
  rw [orthogonalMixedMoment_diag (hankelMomentDet_ne_zero_of_posDef_of_le hL hk.le) hp hdeg]
  exact orthogonalPolynomialNorm_pos_of_posDef hL hk

/-- The positive-order monic subdiagonal is the ratio of mixed diagonal entries. -/
theorem orthogonalRecurrenceBeta_eq_mixed_ratio {L : ℝ[X] →ₗ[ℝ] ℝ} {p : ℕ → ℝ[X]}
    {n k : ℕ} (hL : (hankelMomentMatrix L n).PosDef) (hk : k < n) (hk0 : k ≠ 0)
    (hp : ∀ j, (p j).Monic) (hdeg : ∀ j, (p j).natDegree = j) :
    orthogonalRecurrenceBeta L k =
      orthogonalMixedMoment L p k k / orthogonalMixedMoment L p (k - 1) (k - 1) := by
  rw [orthogonalMixedMoment_diag (hankelMomentDet_ne_zero_of_posDef_of_le hL hk.le)
      (hp k) (hdeg k),
    orthogonalMixedMoment_diag (hankelMomentDet_ne_zero_of_posDef_of_le hL (by omega))
      (hp (k - 1)) (hdeg (k - 1))]
  exact if_neg hk0

/-- The mixed table recovers the actual monic diagonal coefficient at positive
orders, using only finite positive moment data.
atlas: modified-chebyshev-algorithm (partial) -/
theorem orthogonalRecurrenceAlpha_eq_mixed_ratio {L : ℝ[X] →ₗ[ℝ] ℝ} {p : ℕ → ℝ[X]}
    {a b : ℕ → ℝ} {n k : ℕ} (hL : (hankelMomentMatrix L n).PosDef)
    (hk : k < n) (hk0 : k ≠ 0) (hp : ∀ j, (p j).Monic)
    (hdeg : ∀ j, (p j).natDegree = j)
    (hrec : X * p k = p (k + 1) + C (a k) * p k +
      if k = 0 then 0 else C (b k) * p (k - 1)) :
    orthogonalRecurrenceAlpha L k = a k +
      orthogonalMixedMoment L p k (k + 1) / orthogonalMixedMoment L p k k -
      orthogonalMixedMoment L p (k - 1) k / orthogonalMixedMoment L p (k - 1) (k - 1) := by
  have hd (j : ℕ) : (p j).degree = j := by rw [degree_eq_natDegree (hp j).ne_zero, hdeg]
  have hz := orthogonalMixedMoment_eq_zero
    (hankelMomentDet_ne_zero_of_posDef_of_le hL (by omega : k + 1 ≤ n)) (hd k) (by omega)
  have he := orthogonalMixedMoment_succ L p a b k k
    (fun j hj => hankelMomentDet_ne_zero_of_posDef_of_le hL (by omega)) hrec
  rw [hz, if_neg hk0, orthogonalMixedMoment_eq_zero
    (hankelMomentDet_ne_zero_of_posDef_of_le hL hk.le) (hd (k - 1)) (by omega),
    mul_zero, add_zero, orthogonalRecurrenceBeta_eq_mixed_ratio hL hk hk0 hp hdeg] at he
  have hc := (orthogonalMixedMoment_diag_pos hL hk (hp k) (hdeg k)).ne'
  have hpv := (orthogonalMixedMoment_diag_pos hL (by omega : k - 1 < n)
    (hp (k - 1)) (hdeg (k - 1))).ne'
  field_simp [hpv] at he
  field_simp [hc, hpv]
  nlinarith

/-- The initial diagonal is `a₀ + m₁/m₀`. -/
theorem orthogonalRecurrenceAlpha_zero_eq_modified_moments {L : ℝ[X] →ₗ[ℝ] ℝ}
    {p : ℕ → ℝ[X]} {a : ℝ} {n : ℕ} (hL : (hankelMomentMatrix L n).PosDef)
    (hn : 0 < n) (hp0 : p 0 = 1) (hrec : X * p 0 = p 1 + C a * p 0) :
    orthogonalRecurrenceAlpha L 0 = a + L (p 1) / L (p 0) := by
  have hnorm : L (p 0) ≠ 0 := by
    have h := orthogonalPolynomialNorm_pos_of_posDef hL hn
    simpa [orthogonalPolynomialNorm, hp0] using h.ne'
  have he : L X = L (p 1) + a * L (p 0) := by
    have h := congrArg L hrec
    simp only [C_mul', map_add, map_smul, smul_eq_mul] at h
    simpa only [hp0, mul_one] using h
  simp only [orthogonalRecurrenceAlpha, monicOrthogonalPolynomial_zero,
    orthogonalPolynomialNorm, one_pow, mul_one]
  rw [← hp0, he]
  field_simp [hnorm]
  ring

end NLAlib
