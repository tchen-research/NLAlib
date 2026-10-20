import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import NLAlib.Matrix.Basic.QuadForm
import NLAlib.Matrix.Basic.RankOneInverse
import NLAlib.Matrix.Functions.FrameBarrierSelection
import NLAlib.Matrix.Inequalities.SeparatingPSDVector

/-!
# Rank-one barrier updates

This file proves the two matrix potential steps used by the deterministic
rank-one sparsification argument of Batson--Spielman--Srivastava, *Twice-
Ramanujan Sparsifiers* (2008), Section 3.2
([arXiv:0808.0163](https://arxiv.org/abs/0808.0163)):

* a reusable real positive-definite rank-one subtraction lemma (`M - t * v vᵀ`
  stays positive definite when `t ≥ 0` and `t * quadForm M⁻¹ v < 1`), proved with weighted
  Cauchy--Schwarz from the PSD quadratic form, and
* the upper and lower barrier updates: `MU + δU·1 - t·vvᵀ` and
  `ML - δL·1 + t·vvᵀ` are positive definite and their inverse traces do not
  increase relative to the old potentials, whenever the candidate score of `v`
  satisfies `upperScore ... v ≤ 1/t` respectively `1/t ≤ lowerScore ... v`.
  These updates use positive shifts and step size, a nonzero vector, and for
  the lower update the strict potential cap `δL * trace ML⁻¹ < 1`.

The definitions `upperMatrix`, `upperGap`, `upperScore`, `lowerMatrix`,
`lowerGap`, `lowerScore` and the candidate selection
`exists_candidate_inverse` live in `NLAlib.Matrix.Functions.FrameBarrierSelection`;
this file composes those with the rank-one inverse and trace identities of
`NLAlib.Matrix.Basic.RankOneInverse`.
The combined existence theorem proves one selected rank-one step. The finite
iteration and final sparsification bound are separate results.
-/

noncomputable section
set_option autoImplicit false

open scoped Matrix BigOperators

namespace NLAlib
namespace RankOneBarrier

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- `quadForm (v vᵀ) x = (v ⋅ x)²` over the reals. -/
private theorem quadForm_vecMulVec_self_eq_sq (v x : n → ℝ) :
    quadForm (Matrix.vecMulVec v v) x = (dotProduct v x) ^ 2 := by
  simpa only [star_trivial, RCLike.ofReal_real_eq_id, id_eq,
    Real.norm_eq_abs, sq_abs, dotProduct_comm] using quadForm_vecMulVec_star_self v x

omit [DecidableEq n] in
/-- `quadForm (t · v vᵀ) x = t * (v ⋅ x)²` over the reals. -/
private theorem quadForm_smul_vecMulVec_self (t : ℝ) (v x : n → ℝ) :
    quadForm (t • Matrix.vecMulVec v v) x = t * (dotProduct v x) ^ 2 := by
  rw [quadForm_def, Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]
  change t * quadForm (Matrix.vecMulVec v v) x = t * (dotProduct v x) ^ 2
  rw [quadForm_vecMulVec_self_eq_sq]

omit [DecidableEq n] in
/-- `quadForm (M - t · v vᵀ) x = quadForm M x - t * (v ⋅ x)²` over the reals. -/
private theorem quadForm_sub_smul_vecMulVec (M : Matrix n n ℝ) (t : ℝ)
    (v x : n → ℝ) :
    quadForm (M - t • Matrix.vecMulVec v v) x =
      quadForm M x - t * (dotProduct v x) ^ 2 := by
  rw [quadForm_def, Matrix.sub_mulVec, dotProduct_sub]
  change quadForm M x - quadForm (t • Matrix.vecMulVec v v) x =
      quadForm M x - t * (dotProduct v x) ^ 2
  rw [quadForm_smul_vecMulVec_self]

/-- Weighted Cauchy--Schwarz from the PSD quadratic form: for positive definite
`M`, `q = quadForm M⁻¹ v`, every vector `x` satisfies
`(v ⋅ x)² ≤ q * quadForm M x`. -/
private theorem cauchy_sq_le_smul_quadForm {M : Matrix n n ℝ} (hM : M.PosDef)
    {v : n → ℝ} {q : ℝ} (hq : q = quadForm M⁻¹ v)
    (x : n → ℝ) : (dotProduct v x) ^ 2 ≤ q * quadForm M x := by
  let y : n → ℝ := M⁻¹.mulVec v
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det (A := M)).mp hM.isUnit
  have hy : M.mulVec y = v := by
    simp [y, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet]
  have hQy : quadForm M y = q := by
    rw [hq, quadForm_def, hy, quadForm_def]
    simp
    rw [dotProduct_comm]
  have hcs := sq_bilinear_le_quadForm_mul_of_posSemidef hM.posSemidef x y
  simpa only [hy, hQy, dotProduct_comm, mul_comm] using hcs

/-- For positive definite `M` and `t ≥ 0`, the strict bound
`t * quadForm M⁻¹ v < 1` guarantees that `M - t · v vᵀ` is positive definite.
Zero vectors, zero step size, and empty index types are included.
Source: BSS 2008, Section 3.2 rank-one update. -/
theorem _root_.Matrix.PosDef.sub_smul_vecMulVec_self {M : Matrix n n ℝ}
    (hM : M.PosDef) {v : n → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hlt : t * quadForm M⁻¹ v < 1) :
    (M - t • Matrix.vecMulVec v v).PosDef := by
  by_cases hv : v = 0
  · subst v
    simpa using hM
  · let q : ℝ := quadForm M⁻¹ v
    have hq : 0 < q := by
      exact (hM.inv).quadForm_pos hv
    have hlt' : t * q < 1 := by
      simpa [q] using hlt
    have hcauchy : ∀ x : n → ℝ, (dotProduct v x) ^ 2 ≤ q * quadForm M x := by
      intro x
      exact cauchy_sq_le_smul_quadForm hM rfl x
    have hqq : ∀ x : n → ℝ,
        quadForm (M - t • Matrix.vecMulVec v v) x =
          quadForm M x - t * (dotProduct v x) ^ 2 := by
      intro x
      exact quadForm_sub_smul_vecMulVec M t v x
    have hvvherm : (Matrix.vecMulVec v v).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j
      simp [Matrix.vecMulVec_apply, mul_comm]
    exact Matrix.PosDef.of_dotProduct_mulVec_pos
      (hM.isHermitian.sub (Matrix.IsHermitian.smul hvvherm (IsSelfAdjoint.all t)))
      (by
        intro x hx
        rw [← quadForm_def]
        have hmain : 0 < (1 - t * q) * quadForm M x := by
          exact mul_pos (sub_pos.mpr hlt') (hM.quadForm_pos hx)
        calc
          0 < (1 - t * q) * quadForm M x := hmain
          _ ≤ quadForm M x - t * (dotProduct v x) ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_left (hcauchy x) ht]
          _ = quadForm (M - t • Matrix.vecMulVec v v) x := (hqq x).symm)

/-- For positive definite `A` and nonzero `v`, `quadForm (A²) v > 0`. -/
private theorem quadForm_sq_pos_of_posDef {A : Matrix n n ℝ} (hA : A.PosDef)
    {v : n → ℝ} (hv : v ≠ 0) : 0 < quadForm (A ^ 2) v := by
  have hAinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hA.isUnit
  have hsq : (A ^ 2).PosDef := by
    simpa only [pow_two, hA.isHermitian.eq] using
      Matrix.PosDef.conjTranspose_mul_self A hAinj
  exact hsq.quadForm_pos hv

/-- **Upper barrier update.**  If the upper candidate score of a nonzero vector
`v` is at most `1/t`, then `MU + δU·1 - t·v vᵀ` is positive definite and its
inverse trace does not exceed `trace MU⁻¹`.  Source: BSS 2008, Section 3.2
upper barrier step. -/
theorem posDef_and_trace_inv_le_of_upperScore_le [Nonempty n]
    {MU : Matrix n n ℝ} (hMU : MU.PosDef)
    {δU : ℝ} (hδU : 0 < δU) {v : n → ℝ} (hv : v ≠ 0) {t : ℝ} (ht : 0 < t)
    (hscore : upperScore (upperMatrix MU δU) (upperGap MU δU) v ≤ 1 / t) :
    (MU + δU • (1 : Matrix n n ℝ) - t • Matrix.vecMulVec v v).PosDef ∧
      ((MU + δU • (1 : Matrix n n ℝ) - t • Matrix.vecMulVec v v)⁻¹).trace ≤
        MU⁻¹.trace := by
  classical
  set S : Matrix n n ℝ := MU + δU • (1 : Matrix n n ℝ) with hSdef
  set R : Matrix n n ℝ := S⁻¹ with hRdef
  set D : ℝ := upperGap MU δU with hDdef
  set q : ℝ := quadForm R v with hqdef
  set q2 : ℝ := quadForm (R ^ 2) v with hq2def
  have hS : S.PosDef := by
    rw [hSdef]
    exact hMU.add_smul_one_posDef hδU
  have hR : R.PosDef := by
    rw [hRdef]
    exact hS.inv
  have hD : 0 < D := by
    rw [hDdef]
    exact upperGap_pos MU hMU hδU
  have hq : 0 < q := by
    rw [hqdef]
    exact hR.quadForm_pos hv
  have hq2 : 0 < q2 := by
    rw [hq2def]
    exact quadForm_sq_pos_of_posDef hR hv
  have hscore' : quadForm (R ^ 2) v / D + quadForm R v ≤ 1 / t := by
    simpa [upperScore, upperMatrix, upperGap, hRdef] using hscore
  have hsc4 : t * q2 + t * q * D ≤ D := by
    have h0 : (t * D) * (quadForm (R ^ 2) v / D + quadForm R v) ≤
        (t * D) * (1 / t) := by
      exact mul_le_mul_of_nonneg_left hscore' (mul_pos ht hD).le
    have hR0 : (t * D) * (1 / t) = D := by
      field_simp [ht.ne']
    have hL0 : (t * D) * (quadForm (R ^ 2) v / D + quadForm R v) =
        t * quadForm (R ^ 2) v + t * quadForm R v * D := by
      field_simp [hD.ne']
    have h01 : t * quadForm (R ^ 2) v + t * quadForm R v * D ≤ D := by
      rw [hL0, hR0] at h0
      exact h0
    rwa [← hq2def, ← hqdef] at h01
  have htq : t * q < 1 := by
    have hpos2 : 0 < t * q2 := mul_pos ht hq2
    have hm : t * q * D < D := by
      nlinarith [hsc4, hpos2]
    exact lt_of_mul_lt_mul_right (by simpa [one_mul] using hm) hD.le
  have hsc5 : t * q2 ≤ (1 - t * q) * D := by
    nlinarith [hsc4]
  have hsub : (S - t • Matrix.vecMulVec v v).PosDef := by
    exact hS.sub_smul_vecMulVec_self ht.le (by
      rw [← hRdef, ← hqdef]
      exact htq)
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det (A := S)).mp hS.isUnit
  have hvd : dotProduct v (S⁻¹.mulVec v) = q := by
    rw [← hRdef]
    dsimp [q]
    rw [quadForm_def]
    simp
  have hvd2 : dotProduct v ((S⁻¹ * S⁻¹).mulVec v) = q2 := by
    rw [← hRdef]
    dsimp [q2]
    rw [quadForm_def, pow_two]
    simp
  have hden : 1 + (-t) * q = 1 - t * q := by ring
  have hd : 1 + (-t) * (dotProduct v (S⁻¹.mulVec v)) ≠ 0 := by
    rw [hvd, hden]
    exact ne_of_gt (sub_pos.mpr htq)
  have htr := Matrix.trace_mul_inv_add_smul_vecMulVec_self (M := S) (H := 1)
    v (-t) hSdet hd
  have htr1 : ((S - t • Matrix.vecMulVec v v)⁻¹).trace =
      S⁻¹.trace - ((-t) / (1 + (-t) * (dotProduct v (S⁻¹.mulVec v)))) *
        (dotProduct v ((S⁻¹ * S⁻¹).mulVec v)) := by
    calc
      ((S - t • Matrix.vecMulVec v v)⁻¹).trace
          = (1 * (S + (-t) • Matrix.vecMulVec v v)⁻¹).trace := by
            rw [Matrix.one_mul, show S + (-t) • Matrix.vecMulVec v v =
                S - t • Matrix.vecMulVec v v by
              ext i j
              simp [sub_eq_add_neg, neg_smul]]
      _ = S⁻¹.trace - ((-t) / (1 + (-t) * (dotProduct v (S⁻¹.mulVec v)))) *
            (dotProduct v ((S⁻¹ * S⁻¹).mulVec v)) := by
            rw [htr]
            simp
  have htr' : ((S - t • Matrix.vecMulVec v v)⁻¹).trace =
      S⁻¹.trace + (t / (1 - t * q)) * q2 := by
    calc
      ((S - t • Matrix.vecMulVec v v)⁻¹).trace
          = S⁻¹.trace - ((-t) / (1 + (-t) * (dotProduct v (S⁻¹.mulVec v)))) *
              (dotProduct v ((S⁻¹ * S⁻¹).mulVec v)) := htr1
      _ = S⁻¹.trace - ((-t) / (1 - t * q)) * q2 := by
            rw [hvd, hvd2, hden]
      _ = S⁻¹.trace + (t / (1 - t * q)) * q2 := by
            ring
  have htrS : S⁻¹.trace = MU⁻¹.trace - D := by
    rw [hSdef]
    unfold D upperGap upperMatrix
    ring
  have hdenpos : 0 < 1 - t * q := sub_pos.mpr htq
  have hcore : t * q2 / (1 - t * q) ≤ D :=
    (div_le_iff₀ hdenpos).mpr (by simpa [mul_comm, mul_assoc, mul_left_comm] using hsc5)
  refine ⟨hsub, ?_⟩
  rw [htr']
  calc
    S⁻¹.trace + (t / (1 - t * q)) * q2
        = (MU⁻¹.trace - D) + (t / (1 - t * q)) * q2 := by
          rw [htrS]
    _ = MU⁻¹.trace - D + t * q2 / (1 - t * q) := by
          rw [div_mul_eq_mul_div]
    _ ≤ MU⁻¹.trace - D + D := by
          nlinarith [hcore]
    _ = MU⁻¹.trace := by
          ring

/-- **Lower barrier update.**  If `δL * trace ML⁻¹ < 1` and the lower candidate
score of a nonzero vector `v` is at least `1/t`, then `ML - δL·1 + t·v vᵀ`
is positive definite and its inverse trace does not exceed `trace ML⁻¹`.
Source: BSS 2008, Section 3.2 lower barrier step. -/
theorem posDef_and_trace_inv_le_of_le_lowerScore [Nonempty n]
    {ML : Matrix n n ℝ} (hML : ML.PosDef)
    {δL : ℝ} (hδL : 0 < δL) (hcap : δL * ML⁻¹.trace < 1) {v : n → ℝ}
    (hv : v ≠ 0) {t : ℝ} (ht : 0 < t)
    (hscore : 1 / t ≤ lowerScore (lowerMatrix ML δL) (lowerGap ML δL) v) :
    (ML - δL • (1 : Matrix n n ℝ) + t • Matrix.vecMulVec v v).PosDef ∧
      ((ML - δL • (1 : Matrix n n ℝ) + t • Matrix.vecMulVec v v)⁻¹).trace ≤
        ML⁻¹.trace := by
  classical
  set S : Matrix n n ℝ := ML - δL • (1 : Matrix n n ℝ) with hSdef
  set R : Matrix n n ℝ := S⁻¹ with hRdef
  set D : ℝ := lowerGap ML δL with hDdef
  set q : ℝ := quadForm R v with hqdef
  set q2 : ℝ := quadForm (R ^ 2) v with hq2def
  have hS : S.PosDef := by
    rw [hSdef]
    exact hML.sub_smul_one_posDef_of_mul_trace_inv_lt_one hδL hcap
  have hR : R.PosDef := by
    rw [hRdef]
    exact hS.inv
  have hq : 0 < q := by
    rw [hqdef]
    exact hR.quadForm_pos hv
  have hq2 : 0 < q2 := by
    rw [hq2def]
    exact quadForm_sq_pos_of_posDef hR hv
  have hD : 0 < D := by
    rw [hDdef]
    exact lowerGap_pos ML hML hδL hcap
  have hscore' : 1 / t ≤ quadForm (R ^ 2) v / D - quadForm R v := by
    simpa [lowerScore, lowerMatrix, lowerGap, hRdef] using hscore
  have hsc4 : D ≤ t * q2 - t * q * D := by
    have h0 : (t * D) * (1 / t) ≤
        (t * D) * (quadForm (R ^ 2) v / D - quadForm R v) := by
      exact mul_le_mul_of_nonneg_left hscore' (mul_pos ht hD).le
    have hR0 : (t * D) * (1 / t) = D := by
      field_simp [ht.ne']
    have hL0 : (t * D) * (quadForm (R ^ 2) v / D - quadForm R v) =
        t * quadForm (R ^ 2) v - t * quadForm R v * D := by
      field_simp [hD.ne']
    have h01 : D ≤ t * quadForm (R ^ 2) v - t * quadForm R v * D := by
      rw [hR0, hL0] at h0
      exact h0
    rwa [← hq2def, ← hqdef] at h01
  have hsc5 : (1 + t * q) * D ≤ t * q2 := by
    nlinarith [hsc4]
  have hvpsd : (t • Matrix.vecMulVec v v).PosSemidef := by
    exact (Matrix.posSemidef_vecMulVec_self_star v).smul (a := t) ht.le
  have hadd : (S + t • Matrix.vecMulVec v v).PosDef := hS.add_posSemidef hvpsd
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det (A := S)).mp hS.isUnit
  have hvd : dotProduct v (S⁻¹.mulVec v) = q := by
    rw [← hRdef]
    dsimp [q]
    rw [quadForm_def]
    simp
  have hvd2 : dotProduct v ((S⁻¹ * S⁻¹).mulVec v) = q2 := by
    rw [← hRdef]
    dsimp [q2]
    rw [quadForm_def, pow_two]
    simp
  have hdenpos : 0 < 1 + t * q := add_pos zero_lt_one (mul_pos ht hq)
  have hd : 1 + t * (dotProduct v (S⁻¹.mulVec v)) ≠ 0 := by
    rw [hvd]
    exact ne_of_gt hdenpos
  have htr := Matrix.trace_mul_inv_add_smul_vecMulVec_self (M := S) (H := 1)
    v t hSdet hd
  have htr1 : ((S + t • Matrix.vecMulVec v v)⁻¹).trace =
      S⁻¹.trace - (t / (1 + t * (dotProduct v (S⁻¹.mulVec v)))) *
        (dotProduct v ((S⁻¹ * S⁻¹).mulVec v)) := by
    calc
      ((S + t • Matrix.vecMulVec v v)⁻¹).trace
          = (1 * (S + t • Matrix.vecMulVec v v)⁻¹).trace := by
            rw [Matrix.one_mul]
      _ = S⁻¹.trace - (t / (1 + t * (dotProduct v (S⁻¹.mulVec v)))) *
            (dotProduct v ((S⁻¹ * S⁻¹).mulVec v)) := by
            rw [htr]
            simp
  have htr' : ((S + t • Matrix.vecMulVec v v)⁻¹).trace =
      S⁻¹.trace - (t / (1 + t * q)) * q2 := by
    calc
      ((S + t • Matrix.vecMulVec v v)⁻¹).trace
          = S⁻¹.trace - (t / (1 + t * (dotProduct v (S⁻¹.mulVec v)))) *
              (dotProduct v ((S⁻¹ * S⁻¹).mulVec v)) := htr1
      _ = S⁻¹.trace - (t / (1 + t * q)) * q2 := by
            rw [hvd, hvd2]
  have htrS : S⁻¹.trace = ML⁻¹.trace + D := by
    rw [hSdef]
    unfold D lowerGap lowerMatrix
    ring
  have hcore : D ≤ t * q2 / (1 + t * q) :=
    (le_div_iff₀ hdenpos).mpr (by simpa [mul_comm, mul_assoc, mul_left_comm] using hsc5)
  refine ⟨by simpa [hSdef] using hadd, ?_⟩
  rw [htr']
  calc
    S⁻¹.trace - (t / (1 + t * q)) * q2
        = (ML⁻¹.trace + D) - (t / (1 + t * q)) * q2 := by
          rw [htrS]
    _ = ML⁻¹.trace + D - t * q2 / (1 + t * q) := by
          rw [div_mul_eq_mul_div]
    _ ≤ ML⁻¹.trace := by
          linarith [hcore]

/-- **Candidate rank-one step with both barrier updates.**  Under the frame,
positivity, shift and potential hypotheses of `exists_candidate_inverse`, there
is a nonzero frame vector `v i` and a positive step size `t` for which both the
upper and the lower barrier update are positive definite and do not increase
their inverse traces.  Source: BSS 2008, Section 3.2. -/
theorem exists_updates_of_frame {I : Type*} [Fintype I] [Nonempty n]
    (v : I → n → ℝ)
    (hframe : ∑ i, Matrix.vecMulVec (v i) (v i) = 1)
    (MU : Matrix n n ℝ) (hMU : MU.PosDef)
    (ML : Matrix n n ℝ) (hML : ML.PosDef)
    (δU δL : ℝ) (hδU : 0 < δU) (hδL : 0 < δL)
    (hcap : δL * ML⁻¹.trace < 1)
    (hpot : 1 / δU + MU⁻¹.trace ≤ 1 / δL - ML⁻¹.trace) :
    ∃ i, v i ≠ 0 ∧ ∃ t : ℝ, 0 < t ∧
      (MU + δU • (1 : Matrix n n ℝ) - t • Matrix.vecMulVec (v i) (v i)).PosDef ∧
      ((MU + δU • (1 : Matrix n n ℝ) - t • Matrix.vecMulVec (v i) (v i))⁻¹).trace ≤
        MU⁻¹.trace ∧
      (ML - δL • (1 : Matrix n n ℝ) + t • Matrix.vecMulVec (v i) (v i)).PosDef ∧
      ((ML - δL • (1 : Matrix n n ℝ) + t • Matrix.vecMulVec (v i) (v i))⁻¹).trace ≤
        ML⁻¹.trace := by
  obtain ⟨i, hvi, t, ht, hUle, hLge⟩ :=
    exists_candidate_inverse v hframe MU hMU ML hML δU δL hδU hδL hcap hpot
  refine ⟨i, hvi, t, ht, ?_, ?_, ?_, ?_⟩
  · exact (posDef_and_trace_inv_le_of_upperScore_le hMU hδU hvi ht hUle).1
  · exact (posDef_and_trace_inv_le_of_upperScore_le hMU hδU hvi ht hUle).2
  · exact (posDef_and_trace_inv_le_of_le_lowerScore hML hδL hcap hvi ht hLge).1
  · exact (posDef_and_trace_inv_le_of_le_lowerScore hML hδL hcap hvi ht hLge).2

end RankOneBarrier
end NLAlib
