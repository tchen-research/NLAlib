import NLAlib.Krylov.Spectral.RayleighQuotientIteration
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# RQI runs and breakdown

The iteration stops successfully at an exact eigenvector. A singular shift at a
noneigenvector is a distinct breakdown. Infinite runs that avoid breakdown converge to the
selected eigenvector line, with explicit geometric and cubic bounds.
Source: Trefethen–Bau (1997), Lecture 27; Parlett (1998), §4.6.
-/

noncomputable section
open scoped Matrix Topology
open Matrix Filter

namespace NLAlib.RayleighQuotientIteration

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
variable {A : Matrix n n 𝕜}

/-- The three outcomes of inspecting an RQI state. -/
inductive Outcome (n 𝕜 : Type*) where
  /-- Exact eigenvector: successful termination. -/
  | success (x : n → 𝕜)
  /-- A nonsingular inverse step produced the next state. -/
  | next (x : n → 𝕜)
  /-- A singular shift at a noneigenvector. -/
  | breakdown

/-- Inspect a state according to the RQI stopping and breakdown convention. -/
def advance (A : Matrix n n 𝕜) (x : n → 𝕜) : Outcome n 𝕜 := by
  classical
  exact if A *ᵥ x = rayleighQuotient A x • x then .success x
    else if IsUnit (A - rayleighQuotient A x • (1 : Matrix n n 𝕜)) then .next (step A x)
    else .breakdown

/-- Run RQI for at most the given number of transitions, preserving successful termination
and breakdown once either has occurred. At zero transitions the initial state is pending. -/
def run (A : Matrix n n 𝕜) (x₀ : n → 𝕜) : ℕ → Outcome n 𝕜
  | 0 => .next x₀
  | k + 1 => match run A x₀ k with
    | .next x => advance A x
    | .success x => .success x
    | .breakdown => .breakdown

/-- A continuing step is exactly the normalized inverse step at an invertible shift. -/
theorem advance_eq_next_iff (A : Matrix n n 𝕜) (x y : n → 𝕜) :
    advance A x = .next y ↔
      A *ᵥ x ≠ rayleighQuotient A x • x ∧
        IsUnit (A - rayleighQuotient A x • (1 : Matrix n n 𝕜)) ∧ step A x = y := by
  classical
  unfold advance
  split_ifs <;> simp_all

/-- A singular shifted matrix at a noneigenvector is a breakdown.
atlas: rayleigh-quotient-iteration (partial) -/
theorem advance_eq_breakdown_iff (A : Matrix n n 𝕜) (x : n → 𝕜) :
    advance A x = .breakdown ↔ A *ᵥ x ≠ rayleighQuotient A x • x ∧
      ¬ IsUnit (A - rayleighQuotient A x • (1 : Matrix n n 𝕜)) := by
  classical
  unfold advance
  split_ifs <;> simp_all

/-- Successful termination returns exactly the current eigenvector. -/
theorem advance_eq_success_iff (A : Matrix n n 𝕜) (x y : n → 𝕜) :
    advance A x = .success y ↔ A *ᵥ x = rayleighQuotient A x • x ∧ x = y := by
  classical
  unfold advance
  split_ifs <;> simp_all

/-- Along any sequence of valid inverse steps, the target overlap stays nonzero and the
local neighborhood is invariant. -/
theorem run_invariants (hA : A.IsHermitian) {i : n} {g M : ℝ}
    (hg : 0 < g) (hM : 0 < M)
    (hgap : ∀ j, j ≠ i → g ≤ |hA.eigenvalues j - hA.eigenvalues i|)
    (hdiam : ∀ j, j ≠ i → |hA.eigenvalues j - hA.eigenvalues i| ≤ M)
    {x : ℕ → n → 𝕜} (hx : hA.eigenvectorCoordinates (x 0) i ≠ 0)
    (hlocal : tangentSq hA i (x 0) ≤ g / (4 * M))
    (hstep : ∀ k, x (k + 1) = step A (x k))
    (hshift : ∀ k j, hA.eigenvalues j ≠ rayleighQuotient A (x k)) (k : ℕ) :
    hA.eigenvectorCoordinates (x k) i ≠ 0 ∧ tangentSq hA i (x k) ≤ g / (4 * M) := by
  induction k with
  | zero => exact ⟨hx, hlocal⟩
  | succ k ih =>
    rw [hstep]
    exact ⟨(step_norm_and_coordinates_ne_zero hA ih.1 (hshift k)).2.1,
      tangentSq_step_le_neighborhood hA hg hM hgap hdiam ih.1 ih.2 (hshift k)⟩

/-- Every infinite valid RQI run contracts geometrically and cubically in eigenvector-line
angle. The displayed geometric factor equals `2⁻ᵏ`.
atlas: rayleigh-quotient-iteration (partial) -/
theorem run_tangent_le (hA : A.IsHermitian) {i : n} {g M : ℝ}
    (hg : 0 < g) (hM : 0 < M)
    (hgap : ∀ j, j ≠ i → g ≤ |hA.eigenvalues j - hA.eigenvalues i|)
    (hdiam : ∀ j, j ≠ i → |hA.eigenvalues j - hA.eigenvalues i| ≤ M)
    {x : ℕ → n → 𝕜} (hx : hA.eigenvectorCoordinates (x 0) i ≠ 0)
    (hlocal : tangentSq hA i (x 0) ≤ g / (4 * M))
    (hstep : ∀ k, x (k + 1) = step A (x k))
    (hshift : ∀ k j, hA.eigenvalues j ≠ rayleighQuotient A (x k)) (k : ℕ) :
    tangent hA i (x (k + 1)) ≤ (2 * M / g) * tangent hA i (x k) ^ 3 ∧
      tangent hA i (x k) ≤ (1 / 2 : ℝ) ^ k * tangent hA i (x 0) := by
  have hinv := run_invariants hA hg hM hgap hdiam hx hlocal hstep hshift
  have hcontract (j : ℕ) := tangent_step_le hA hg hM hgap hdiam
    (hinv j).1 (hinv j).2 (hshift j)
  constructor
  · rw [hstep]; exact (hcontract k).1
  · induction k with
    | zero => simp
    | succ k ih =>
      rw [hstep]
      calc
        _ ≤ tangent hA i (x k) / 2 := (hcontract k).2
        _ ≤ ((1 / 2 : ℝ) ^ k * tangent hA i (x 0)) / 2 := by linarith
        _ = (1 / 2 : ℝ) ^ (k + 1) * tangent hA i (x 0) := by rw [pow_succ]; ring

/-- The eigenvector-line angle of every infinite valid local RQI run tends to zero.
atlas: rayleigh-quotient-iteration (partial) -/
theorem tendsto_tangent_run (hA : A.IsHermitian) {i : n} {g M : ℝ}
    (hg : 0 < g) (hM : 0 < M)
    (hgap : ∀ j, j ≠ i → g ≤ |hA.eigenvalues j - hA.eigenvalues i|)
    (hdiam : ∀ j, j ≠ i → |hA.eigenvalues j - hA.eigenvalues i| ≤ M)
    {x : ℕ → n → 𝕜} (hx : hA.eigenvectorCoordinates (x 0) i ≠ 0)
    (hlocal : tangentSq hA i (x 0) ≤ g / (4 * M))
    (hstep : ∀ k, x (k + 1) = step A (x k))
    (hshift : ∀ k j, hA.eigenvalues j ≠ rayleighQuotient A (x k)) :
    Tendsto (fun k => tangent hA i (x k)) atTop (𝓝 0) := by
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
      (tangent hA i (x 0))
  simp only [zero_mul] at hpow
  exact squeeze_zero (fun _ => Real.sqrt_nonneg _)
    (fun k => (run_tangent_le hA hg hM hgap hdiam hx hlocal hstep hshift k).2) hpow

/-- The Rayleigh quotients of every infinite valid local RQI run converge to the target
eigenvalue. No scalar cubic convergence is asserted for an interior eigenvalue.
atlas: rayleigh-quotient-iteration (partial) -/
theorem tendsto_rayleighQuotient_run (hA : A.IsHermitian) {i : n} {g M : ℝ}
    (hg : 0 < g) (hM : 0 < M)
    (hgap : ∀ j, j ≠ i → g ≤ |hA.eigenvalues j - hA.eigenvalues i|)
    (hdiam : ∀ j, j ≠ i → |hA.eigenvalues j - hA.eigenvalues i| ≤ M)
    {x : ℕ → n → 𝕜} (hx : hA.eigenvectorCoordinates (x 0) i ≠ 0)
    (hlocal : tangentSq hA i (x 0) ≤ g / (4 * M))
    (hstep : ∀ k, x (k + 1) = step A (x k))
    (hshift : ∀ k j, hA.eigenvalues j ≠ rayleighQuotient A (x k)) :
    Tendsto (fun k => rayleighQuotient A (x k)) atTop (𝓝 (hA.eigenvalues i)) := by
  have ht := tendsto_tangent_run hA hg hM hgap hdiam hx hlocal hstep hshift
  have hq : Tendsto (fun k => M * tangent hA i (x k) ^ 2) atTop (𝓝 0) := by
    simpa using (ht.pow 2).const_mul M
  have herr (k : ℕ) : |rayleighQuotient A (x k) - hA.eigenvalues i| ≤
      M * tangent hA i (x k) ^ 2 := by
    rw [tangent_sq]
    have hinv := run_invariants hA hg hM hgap hdiam hx hlocal hstep hshift k
    apply (abs_rayleighQuotient_sub_le hA hdiam hinv.1).trans
    have hnonneg := tangentSq_nonneg hA i (x k)
    apply (div_le_iff₀ (show 0 < 1 + tangentSq hA i (x k) by positivity)).2
    nlinarith [mul_nonneg (mul_nonneg hM.le hnonneg) hnonneg]
  have he := squeeze_zero (fun k => abs_nonneg (rayleighQuotient A (x k) - hA.eigenvalues i))
    herr hq
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using he)

/-- Successful termination at a vector with nonzero target overlap necessarily returns
the target eigenvalue, not another eigenvalue. -/
theorem eigenvalue_eq_of_advance_success (hA : A.IsHermitian) {i : n} {x y : n → 𝕜}
    (hx : hA.eigenvectorCoordinates x i ≠ 0) (hsuccess : advance A x = .success y) :
    y = x ∧ rayleighQuotient A x = hA.eigenvalues i ∧ A *ᵥ y = hA.eigenvalues i • y := by
  obtain ⟨heig, rfl⟩ := (advance_eq_success_iff A x y).mp hsuccess
  have hc := congrArg (fun v => hA.eigenvectorCoordinates v i) heig
  rw [hA.eigenvectorCoordinates_mulVec, RCLike.real_smul_eq_coe_smul (K := 𝕜),
    hA.eigenvectorCoordinates_smul, Pi.smul_apply, smul_eq_mul] at hc
  have heq : hA.eigenvalues i = rayleighQuotient A x :=
    RCLike.ofReal_injective (mul_right_cancel₀ hx hc)
  exact ⟨rfl, heq.symm, by simpa only [heq] using heig⟩

/-- Infinite runs phrased through the actual stopping/breakdown transition satisfy both
line-angle and Rayleigh-quotient convergence.
atlas: rayleigh-quotient-iteration (partial) -/
theorem tendsto_of_advance_next (hA : A.IsHermitian) {i : n} {g M : ℝ}
    (hg : 0 < g) (hM : 0 < M)
    (hgap : ∀ j, j ≠ i → g ≤ |hA.eigenvalues j - hA.eigenvalues i|)
    (hdiam : ∀ j, j ≠ i → |hA.eigenvalues j - hA.eigenvalues i| ≤ M)
    {x : ℕ → n → 𝕜} (hx : hA.eigenvectorCoordinates (x 0) i ≠ 0)
    (hlocal : tangentSq hA i (x 0) ≤ g / (4 * M))
    (hadvance : ∀ k, advance A (x k) = .next (x (k + 1))) :
    Tendsto (fun k => tangent hA i (x k)) atTop (𝓝 0) ∧
      Tendsto (fun k => rayleighQuotient A (x k)) atTop (𝓝 (hA.eigenvalues i)) := by
  have hs (k : ℕ) := (advance_eq_next_iff A (x k) (x (k + 1))).mp (hadvance k)
  have hstep (k : ℕ) : x (k + 1) = step A (x k) := (hs k).2.2.symm
  have hshift (k : ℕ) := (hA.isUnit_sub_smul_one_iff_eigenvalues_ne _).mp (hs k).2.1
  exact ⟨tendsto_tangent_run hA hg hM hgap hdiam hx hlocal hstep hshift,
    tendsto_rayleighQuotient_run hA hg hM hgap hdiam hx hlocal hstep hshift⟩

/-- Every active or successfully terminated finite run retains normalization, nonzero
target overlap, and the invariant neighborhood. A breakdown makes no output-vector claim. -/
theorem run_state_invariants (hA : A.IsHermitian) {i : n} {g M : ℝ}
    (hg : 0 < g) (hM : 0 < M)
    (hgap : ∀ j, j ≠ i → g ≤ |hA.eigenvalues j - hA.eigenvalues i|)
    (hdiam : ∀ j, j ≠ i → |hA.eigenvalues j - hA.eigenvalues i| ≤ M)
    {x₀ : n → 𝕜} (hunit : ‖WithLp.toLp 2 x₀‖ = 1)
    (hx : hA.eigenvectorCoordinates x₀ i ≠ 0)
    (hlocal : tangentSq hA i x₀ ≤ g / (4 * M)) (k : ℕ) :
    match run A x₀ k with
    | .breakdown => True
    | .success y | .next y => ‖WithLp.toLp 2 y‖ = 1 ∧
        hA.eigenvectorCoordinates y i ≠ 0 ∧ tangentSq hA i y ≤ g / (4 * M) := by
  induction k with
  | zero => exact ⟨hunit, hx, hlocal⟩
  | succ k ih =>
    simp only [run]
    cases hstate : run A x₀ k with
    | breakdown => trivial
    | success y => simpa only [hstate] using ih
    | next y =>
      have hy : ‖WithLp.toLp 2 y‖ = 1 ∧ hA.eigenvectorCoordinates y i ≠ 0 ∧
          tangentSq hA i y ≤ g / (4 * M) := by simpa only [hstate] using ih
      dsimp only
      unfold advance
      split_ifs with hterm hsolve
      · exact hy
      · have hshift := (hA.isUnit_sub_smul_one_iff_eigenvalues_ne _).mp hsolve
        have hp := step_norm_and_coordinates_ne_zero hA hy.2.1 hshift
        exact ⟨hp.1, hp.2.1,
          tangentSq_step_le_neighborhood hA hg hM hgap hdiam hy.2.1 hy.2.2 hshift⟩
      · trivial

/-- The successful outcome of a finite run is an actual Rayleigh eigenvector. -/
theorem mulVec_eq_rayleighQuotient_smul_of_run_success (A : Matrix n n 𝕜)
    (x₀ : n → 𝕜) (k : ℕ) {y : n → 𝕜} (hsuccess : run A x₀ k = .success y) :
    A *ᵥ y = rayleighQuotient A y • y := by
  induction k with
  | zero => cases hsuccess
  | succ k ih =>
    simp only [run] at hsuccess
    cases hstate : run A x₀ k with
    | breakdown => simp [hstate] at hsuccess
    | success z =>
      simp only [hstate, Outcome.success.injEq] at hsuccess
      subst z
      exact ih hstate
    | next z =>
      simp only [hstate] at hsuccess
      obtain ⟨he, rfl⟩ := (advance_eq_success_iff A z y).mp hsuccess
      exact he

/-- Any successful finite local RQI run returns a unit eigenvector for the selected target
eigenvalue. Interior-eigenvalue breakdown is kept distinct from successful termination.
atlas: rayleigh-quotient-iteration (partial) -/
theorem run_success_target (hA : A.IsHermitian) {i : n} {g M : ℝ}
    (hg : 0 < g) (hM : 0 < M)
    (hgap : ∀ j, j ≠ i → g ≤ |hA.eigenvalues j - hA.eigenvalues i|)
    (hdiam : ∀ j, j ≠ i → |hA.eigenvalues j - hA.eigenvalues i| ≤ M)
    {x₀ : n → 𝕜} (hunit : ‖WithLp.toLp 2 x₀‖ = 1)
    (hx : hA.eigenvectorCoordinates x₀ i ≠ 0)
    (hlocal : tangentSq hA i x₀ ≤ g / (4 * M)) {k : ℕ} {y : n → 𝕜}
    (hsuccess : run A x₀ k = .success y) :
    ‖WithLp.toLp 2 y‖ = 1 ∧ rayleighQuotient A y = hA.eigenvalues i ∧
      A *ᵥ y = hA.eigenvalues i • y := by
  have hinv := run_state_invariants hA hg hM hgap hdiam hunit hx hlocal k
  rw [hsuccess] at hinv
  have he := mulVec_eq_rayleighQuotient_smul_of_run_success A x₀ k hsuccess
  have hs : advance A y = .success y := (advance_eq_success_iff A y y).mpr ⟨he, rfl⟩
  have ht := eigenvalue_eq_of_advance_success hA hinv.2.1 hs
  exact ⟨hinv.1, ht.2.1, ht.2.2⟩

end NLAlib.RayleighQuotientIteration
