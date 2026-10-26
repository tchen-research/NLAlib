import NLAlib.Polynomial.OrthogonalPolynomials.ModifiedChebyshevIdentities

/-!
# The finite modified Chebyshev algorithm

The state stores two consecutive mixed-moment rows and the newly recovered
recurrence coefficients. The initial `beta` stores total mass, as in Gautschi's
algorithm; it is omitted from the row-zero recurrence. At positive orders it is
the native monic recurrence coefficient. The proof only examines entries with
`k+l < 2n`, so no higher input moment is required.
Source: Gautschi (2004), Algorithm 2.1.
-/

noncomputable section
open Polynomial
namespace NLAlib

/-- Two mixed-moment rows and the current recovered recurrence coefficients.
At order zero, `beta` stores the mass; the preceding row is zero. -/
structure ModifiedChebyshevState where
  /-- The preceding mixed-moment row. -/
  prev : ℕ → ℝ
  /-- The current mixed-moment row. -/
  row : ℕ → ℝ
  /-- The current monic diagonal coefficient. -/
  alpha : ℝ
  /-- Total mass at order zero, and the monic subdiagonal at positive orders. -/
  beta : ℝ

/-- Initial state from supplied modified moments, with total division on invalid
inputs. The correctness theorem proves the input mass is positive. -/
def modifiedChebyshevInit (a m : ℕ → ℝ) : ModifiedChebyshevState :=
  ⟨0, m, a 0 + m 1 / m 0, m 0⟩

/-- One row update of the modified Chebyshev algorithm. No moment functional or
orthogonal polynomial occurs in this executable algebraic definition. -/
def modifiedChebyshevStep (a b : ℕ → ℝ) (k : ℕ) (s : ModifiedChebyshevState) :
    ModifiedChebyshevState :=
  let r := fun l => s.row (l + 1) + (a l - s.alpha) * s.row l -
    (if k = 0 then 0 else s.beta) * s.prev l +
      if l = 0 then 0 else b l * s.row (l - 1)
  ⟨s.row, r, a (k + 1) + r (k + 2) / r (k + 1) - s.row (k + 1) / s.row k,
    r (k + 1) / s.row k⟩

/-- The actual total modified Chebyshev recurrence. Requested output at order
`k<n` uses only input moments of indices below `2n`. -/
def modifiedChebyshevState (a b m : ℕ → ℝ) : ℕ → ModifiedChebyshevState
  | 0 => modifiedChebyshevInit a m
  | k + 1 => modifiedChebyshevStep a b k (modifiedChebyshevState a b m k)

/-- The computed table and coefficients are exactly the canonical finite moment
data. This proves the algorithm itself, allowing arbitrary input extensions above
degree `2n-1` and including an empty requested output when `n=0`.
atlas: modified-chebyshev-algorithm (partial) -/
theorem modifiedChebyshevState_correct (L : ℝ[X] →ₗ[ℝ] ℝ) (p : ℕ → ℝ[X])
    (a b m : ℕ → ℝ) (n : ℕ) (hL : (hankelMomentMatrix L n).PosDef)
    (hp : ∀ j, (p j).Monic) (hdeg : ∀ j, (p j).natDegree = j)
    (hrec : ∀ j, X * p j = p (j + 1) + C (a j) * p j +
      if j = 0 then 0 else C (b j) * p (j - 1))
    (hm : ∀ l < 2 * n, m l = L (p l)) :
    ∀ k < n,
      (∀ l, k + l < 2 * n →
        (modifiedChebyshevState a b m k).row l = orthogonalMixedMoment L p k l) ∧
      (∀ l, k + l < 2 * n →
        (modifiedChebyshevState a b m k).prev l =
          if k = 0 then 0 else orthogonalMixedMoment L p (k - 1) l) ∧
      (modifiedChebyshevState a b m k).alpha = orthogonalRecurrenceAlpha L k ∧
      (modifiedChebyshevState a b m k).beta =
        if k = 0 then L (p 0) else orthogonalRecurrenceBeta L k := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l hl
      simpa only [modifiedChebyshevState, modifiedChebyshevInit,
        orthogonalMixedMoment_zero] using hm l (by omega)
    · intro l _
      rfl
    · change a 0 + m 1 / m 0 = _
      rw [hm 0 (by omega), hm 1 (by omega)]
      exact (orthogonalRecurrenceAlpha_zero_eq_modified_moments hL hk
        (eq_one_of_monic_natDegree_zero (hp 0) (hdeg 0)) (by simpa using hrec 0)).symm
    · change m 0 = L (p 0)
      exact hm 0 (by omega)
  | succ k ih =>
    intro hk
    obtain ⟨hrow, hprev, halpha, hbeta⟩ := ih (by omega)
    let s := modifiedChebyshevState a b m k
    have hcoef : (if k = 0 then 0 else s.beta) = orthogonalRecurrenceBeta L k := by
      by_cases hk0 : k = 0
      · simp [hk0, orthogonalRecurrenceBeta]
      · simp only [s, hbeta, if_neg hk0]
    have hnew : ∀ l, k + 1 + l < 2 * n →
        (modifiedChebyshevStep a b k s).row l = orthogonalMixedMoment L p (k + 1) l := by
      intro l hl
      change s.row (l + 1) + (a l - s.alpha) * s.row l -
        (if k = 0 then 0 else s.beta) * s.prev l +
        (if l = 0 then 0 else b l * s.row (l - 1)) = _
      rw [hcoef]
      change (modifiedChebyshevState a b m k).row (l + 1) +
        (a l - (modifiedChebyshevState a b m k).alpha) *
        (modifiedChebyshevState a b m k).row l -
        orthogonalRecurrenceBeta L k * (modifiedChebyshevState a b m k).prev l + _ = _
      rw [hrow (l + 1) (by omega), halpha, hrow l (by omega), hprev l (by omega),
        orthogonalMixedMoment_succ L p a b k l
          (fun j hj => hankelMomentDet_ne_zero_of_posDef_of_le hL (by omega)) (hrec l)]
      have hbprev : orthogonalRecurrenceBeta L k *
          (if k = 0 then 0 else orthogonalMixedMoment L p (k - 1) l) =
          orthogonalRecurrenceBeta L k * orthogonalMixedMoment L p (k - 1) l := by
        by_cases hk0 : k = 0 <;> simp [hk0, orthogonalRecurrenceBeta]
      rw [hbprev]
      by_cases hl0 : l = 0
      · simp only [if_pos hl0]
      · simp only [if_neg hl0]
        rw [show s.row (l - 1) = orthogonalMixedMoment L p k (l - 1) from hrow _ (by omega)]
    refine ⟨hnew, ?_, ?_, ?_⟩
    · intro l hl
      simpa only [modifiedChebyshevState, modifiedChebyshevStep, Nat.add_sub_cancel,
        Nat.succ_ne_zero, if_false] using hrow l (by omega)
    · change a (k + 1) + (modifiedChebyshevStep a b k s).row (k + 2) /
          (modifiedChebyshevStep a b k s).row (k + 1) - s.row (k + 1) / s.row k = _
      rw [hnew (k + 2) (by omega), hnew (k + 1) (by omega),
        show s.row (k + 1) = _ from hrow (k + 1) (by omega),
        show s.row k = _ from hrow k (by omega)]
      simpa only [Nat.add_sub_cancel] using
        (orthogonalRecurrenceAlpha_eq_mixed_ratio hL hk (by omega) hp hdeg (hrec (k + 1))).symm
    · change (modifiedChebyshevStep a b k s).row (k + 1) / s.row k = _
      rw [hnew (k + 1) (by omega), show s.row k = _ from hrow k (by omega), if_neg (by omega)]
      simpa only [Nat.add_sub_cancel] using
        (orthogonalRecurrenceBeta_eq_mixed_ratio hL hk (by omega) hp hdeg).symm

/-- Every diagonal used as a denominator by the requested finite execution is
strictly positive, as a consequence of the supplied moments.
atlas: modified-chebyshev-algorithm (partial) -/
theorem modifiedChebyshevState_diagonal_pos (L : ℝ[X] →ₗ[ℝ] ℝ) (p : ℕ → ℝ[X])
    (a b m : ℕ → ℝ) (n : ℕ) (hL : (hankelMomentMatrix L n).PosDef)
    (hp : ∀ j, (p j).Monic) (hdeg : ∀ j, (p j).natDegree = j)
    (hrec : ∀ j, X * p j = p (j + 1) + C (a j) * p j +
      if j = 0 then 0 else C (b j) * p (j - 1))
    (hm : ∀ l < 2 * n, m l = L (p l)) (k : ℕ) (hk : k < n) :
    0 < (modifiedChebyshevState a b m k).row k := by
  rw [(modifiedChebyshevState_correct L p a b m n hL hp hdeg hrec hm k hk).1 k (by omega)]
  exact orthogonalMixedMoment_diag_pos hL hk (hp k) (hdeg k)

/-- Finite input and finite output form of the modified Chebyshev algorithm. The
zero extension is only a totalization convention beyond the supplied moments. -/
def modifiedChebyshevCoefficients (a b : ℕ → ℝ) {n : ℕ} (m : Fin (2 * n) → ℝ)
    (k : Fin n) : ℝ × ℝ :=
  let s := modifiedChebyshevState a b (fun l => if h : l < 2 * n then m ⟨l, h⟩ else 0) k
  (s.alpha, s.beta)

/-- The finite algorithm returns precisely the canonical recurrence coefficients,
with the source convention that the zeroth `beta` is total mass.
atlas: modified-chebyshev-algorithm (partial) -/
theorem modifiedChebyshevCoefficients_eq (L : ℝ[X] →ₗ[ℝ] ℝ) (p : ℕ → ℝ[X])
    (a b : ℕ → ℝ) (n : ℕ) (hL : (hankelMomentMatrix L n).PosDef)
    (hp : ∀ j, (p j).Monic) (hdeg : ∀ j, (p j).natDegree = j)
    (hrec : ∀ j, X * p j = p (j + 1) + C (a j) * p j +
      if j = 0 then 0 else C (b j) * p (j - 1)) (k : Fin n) :
    modifiedChebyshevCoefficients a b (fun i : Fin (2 * n) => L (p i)) k =
      (orthogonalRecurrenceAlpha L k,
        if (k : ℕ) = 0 then L (p 0) else orthogonalRecurrenceBeta L k) := by
  have h := modifiedChebyshevState_correct L p a b
    (fun l => if h : l < 2 * n then L (p (⟨l, h⟩ : Fin (2 * n))) else 0)
    n hL hp hdeg hrec (by intro l hl; simp only [dif_pos hl]) k k.isLt
  exact Prod.ext h.2.2.1 h.2.2.2

end NLAlib
