import NLAlib.Estimation.Reconstruction.ChebyshevMomentTail
import NLAlib.Estimation.Reconstruction.ChebyshevSpectralDensity
import NLAlib.Krylov.QueryModel.SubspaceIteration

/-!
# Shared Chebyshev recurrences as a matrix-vector query program

The program stores the previously computed vectors, asks only for the active
prefix at each degree, and updates its table. Each active column costs exactly
one scalar vector query. Matrix entries are never inspected by the program.
Source: MMRS Section 5, the shared three-term recurrence realization.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Polynomial
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exact product count through a given recurrence degree. -/
def chebyshevQueryCount (a : ℝ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => chebyshevProbeCount a (j + 1) + chebyshevQueryCount a j

/-- The recursive budget is exactly the sum of the active prefix widths. -/
theorem chebyshevQueryCount_eq_sum (a : ℝ) (k : ℕ) :
    chebyshevQueryCount a k = ∑ j ∈ Finset.Icc 1 k, chebyshevProbeCount a j := by
  induction k with
  | zero => simp [chebyshevQueryCount]
  | succ k ih =>
    rw [chebyshevQueryCount, ih, Finset.sum_Icc_succ_top (by omega)]
    omega

private def probeIndex {a : ℝ} (ha : 0 ≤ a) (j : ℕ)
    (i : Fin (chebyshevProbeCount a (j + 1))) : Fin (chebyshevProbeCount a 1) :=
  i.castLE (chebyshevProbeCount_antitone ha (by simp)
    (show 1 ≤ j + 1 by omega) (by omega))

/-- One shared recurrence stage. Its responses are the matrix products of
the active vectors; all remaining operations are oracle-free. -/
def chebyshevTableStep (a : ℝ) (ha : 0 ≤ a) (S : ℝ) (j : ℕ)
    (V : ℕ → Matrix n (Fin (chebyshevProbeCount a 1)) ℝ) :
    QueryProgram (n → ℝ) (n → ℝ)
      (ℕ → Matrix n (Fin (chebyshevProbeCount a 1)) ℝ) (chebyshevProbeCount a (j + 1)) :=
  (QueryProgram.family (fun i => S⁻¹ • (V j).col (probeIndex ha j i))).map fun responses =>
    Function.update V (j + 1) (fun r i =>
      if hi : i.val < chebyshevProbeCount a (j + 1) then
        if j = 0 then responses ⟨i.val, hi⟩ r
        else 2 * responses ⟨i.val, hi⟩ r - V (j - 1) r i
      else 0)

/-- The shared recurrence table program, chosen from the probes and scale
before the matrix oracle is supplied. -/
def chebyshevTableProgram (a : ℝ) (ha : 0 ≤ a) (S : ℝ)
    (G : Matrix n (Fin (chebyshevProbeCount a 1)) ℝ) :
    (k : ℕ) → QueryProgram (n → ℝ) (n → ℝ)
      (ℕ → Matrix n (Fin (chebyshevProbeCount a 1)) ℝ) (chebyshevQueryCount a k)
  | 0 => .pure (fun _ => G)
  | k + 1 => (chebyshevTableProgram a ha S G k).bind (chebyshevTableStep a ha S k)

private theorem chebyshev_next_mulVec (B : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) :
    (aeval B (Chebyshev.T ℝ ((j + 1 : ℕ) : ℤ))) *ᵥ b =
      if j = 0 then B *ᵥ ((aeval B (Chebyshev.T ℝ (j : ℤ))) *ᵥ b)
      else (2 : ℝ) • (B *ᵥ ((aeval B (Chebyshev.T ℝ (j : ℤ))) *ᵥ b)) -
        (aeval B (Chebyshev.T ℝ ((j - 1 : ℕ) : ℤ))) *ᵥ b := by
  by_cases hj : j = 0
  · subst j
    simp
  · rw [if_neg hj]
    have hjpos : 1 ≤ j := by omega
    rw [Nat.cast_add, Nat.cast_one, Chebyshev.T_add_one,
      map_sub, map_mul, map_mul, map_ofNat, aeval_X, Matrix.sub_mulVec]
    rw [show (j : ℤ) - 1 = ((j - 1 : ℕ) : ℤ) by omega]
    congr 1
    simp only [show (2 : Matrix n n ℝ) = (2 : ℝ) • (1 : Matrix n n ℝ) by
      ext i l; simp [Matrix.ofNat_apply, Matrix.one_apply], Matrix.smul_mul,
      Matrix.one_mul, Matrix.smul_mulVec, Matrix.mulVec_mulVec]

/-- At every completed degree, all active vectors in the table equal the
corresponding Chebyshev polynomial applied to their original probe. -/
theorem run_chebyshevTableProgram_apply (A : Matrix n n ℝ) (a : ℝ) (ha : 0 ≤ a)
    (S : ℝ) (G : Matrix n (Fin (chebyshevProbeCount a 1)) ℝ) (k j : ℕ) (hj : j ≤ k)
    (i : Fin (chebyshevProbeCount a 1)) (hi : j = 0 ∨ i.val < chebyshevProbeCount a j) :
    ((chebyshevTableProgram a ha S G k).run A.mulVec j).col i =
      (aeval (S⁻¹ • A) (Chebyshev.T ℝ (j : ℤ))) *ᵥ G.col i := by
  induction k generalizing j i with
  | zero =>
    have : j = 0 := by omega
    subst j
    simp [chebyshevTableProgram, QueryProgram.run]
  | succ k ih =>
    by_cases hjlast : j = k + 1
    · subst j
      have hia : i.val < chebyshevProbeCount a (k + 1) := hi.resolve_left (by omega)
      have hik : k = 0 ∨ i.val < chebyshevProbeCount a k := by
        by_cases hk : k = 0
        · exact Or.inl hk
        · exact Or.inr (hia.trans_le (chebyshevProbeCount_antitone ha
            (by change 1 ≤ k; omega) (by change 1 ≤ k + 1; omega) (by omega)))
      have hcur := ih k le_rfl i hik
      have hprev : k - 1 = 0 ∨ i.val < chebyshevProbeCount a (k - 1) := by
        by_cases hk : k - 1 = 0
        · exact Or.inl hk
        · exact Or.inr (hia.trans_le (chebyshevProbeCount_antitone ha
            (by change 1 ≤ k - 1; omega) (by change 1 ≤ k + 1; omega) (by omega)))
      have hpr := ih (k - 1) (by omega) i hprev
      rw [chebyshevTableProgram, QueryProgram.run_bind, chebyshevTableStep,
        QueryProgram.run_map, QueryProgram.run_family, Function.update_self,
        chebyshev_next_mulVec]
      have hindex : probeIndex ha k ⟨i.val, hia⟩ = i := Fin.ext rfl
      ext r
      simp only [Matrix.col_apply, dif_pos hia, hindex, Matrix.mulVec_smul,
        Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
      have hp := congrFun hpr r
      by_cases hk : k = 0
      · simp only [if_pos hk, Pi.smul_apply, smul_eq_mul]
        rw [hcur]
      · simp only [if_neg hk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [hcur]
        exact congrArg (fun x : ℝ => 2 * (S⁻¹ * (A *ᵥ
          ((aeval (S⁻¹ • A)) (Chebyshev.T ℝ (k : ℤ)) *ᵥ G.col i)) r) - x) hp
    · have hjk : j ≤ k := by omega
      rw [chebyshevTableProgram, QueryProgram.run_bind, chebyshevTableStep,
        QueryProgram.run_map, QueryProgram.run_family, Function.update_of_ne hjlast]
      exact ih j hjk i hi

/-- Read the normalized quadratic-form moments from the shared recurrence
table, with no further oracle queries. -/
def chebyshevMomentProgram (a : ℝ) (ha : 0 ≤ a) (S : ℝ)
    (G : Matrix n (Fin (chebyshevProbeCount a 1)) ℝ) (k : ℕ) :
    QueryProgram (n → ℝ) (n → ℝ) (ℕ → ℝ) (chebyshevQueryCount a k) :=
  (chebyshevTableProgram a ha S G k).map fun V j =>
    if hj : 1 ≤ j then
      ((∑ t : Fin (chebyshevProbeCount a j),
        G.col (t.castLE (chebyshevProbeCount_antitone ha (by simp) hj hj)) ⬝ᵥ
          (V j).col (t.castLE (chebyshevProbeCount_antitone ha (by simp) hj hj))) /
        chebyshevProbeCount a j) / Fintype.card n
    else 1

/-- Every requested degree computed by the interaction tree is the actual
shared-prefix Hutchinson estimate. -/
theorem run_chebyshevMomentProgram_apply (A : Matrix n n ℝ) (a : ℝ) (ha : 0 ≤ a)
    (S : ℝ) (G : Matrix n (Fin (chebyshevProbeCount a 1)) ℝ) (k j : ℕ)
    (hj : j ∈ Finset.Icc 1 k) :
    (chebyshevMomentProgram a ha S G k).run A.mulVec j =
      chebyshevTraceMomentEstimate (S⁻¹ • A) a ha G j := by
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hjk := (Finset.mem_Icc.mp hj).2
  simp only [chebyshevMomentProgram, QueryProgram.run_map, dif_pos hj1,
    chebyshevTraceMomentEstimate, hutchinsonEstimate, Fintype.card_fin]
  congr 2
  apply Finset.sum_congr rfl
  intro t ht
  rw [run_chebyshevTableProgram_apply A a ha S G k j hjk _ (Or.inr t.isLt)]
  rfl

/-- Full density estimator program: the recurrence consumes matrix-vector
products, while simplex reconstruction and positive scaling are postprocessing. -/
def chebyshevDensityProgram (k : ℕ) (hk : 1 ≤ k) (S δ : ℝ)
    (G : Matrix n (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) ℝ) :
    QueryProgram (n → ℝ) (n → ℝ) (MeasureTheory.Measure ℝ)
      (chebyshevQueryCount (chebyshevProbeBudget (Fintype.card n) k δ) k) :=
  (chebyshevMomentProgram _ (chebyshevProbeBudget_nonneg _ _ _) S G k).map fun mhat =>
    (chebyshevGridLaw (chebyshevRegressionWeights k hk mhat)).map (fun x => S * x)

/-- The oracle program realizes the actual scaled probability-law estimator,
for every matrix and every probe array, before imposing any random law.
atlas: chebyshev-spectral-density-query (partial) -/
theorem run_chebyshevDensityProgram (A : Matrix n n ℝ) (k : ℕ) (hk : 1 ≤ k) (S δ : ℝ)
    (G : Matrix n (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) ℝ) :
    (chebyshevDensityProgram k hk S δ G).run A.mulVec =
      (chebyshevSpectralDensityEstimate (S⁻¹ • A) k hk δ G).map (fun x => S * x) := by
  simp only [chebyshevDensityProgram, QueryProgram.run_map, chebyshevSpectralDensityEstimate]
  congr 2
  apply chebyshevRegressionWeights_congr
  intro j hj
  exact run_chebyshevMomentProgram_apply A _ _ S G k j hj

/-- An oracle-independent algorithm realizes the decreasing-probe estimate
with the exact sum of its active-prefix counts.
atlas: chebyshev-spectral-density-query (partial) -/
theorem exists_matvecAlg_chebyshevSpectralDensityEstimate (k : ℕ) (hk : 1 ≤ k) (S δ : ℝ)
    (G : Matrix n (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) ℝ) :
    ∃ alg : MatvecAlg ℝ n (MeasureTheory.Measure ℝ),
      alg.cost = ∑ j ∈ Finset.Icc 1 k,
        chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) j ∧
      ∀ A : Matrix n n ℝ, alg.run A =
        (chebyshevSpectralDensityEstimate (S⁻¹ • A) k hk δ G).map (fun x => S * x) := by
  exact ⟨⟨_, chebyshevDensityProgram k hk S δ G⟩,
    chebyshevQueryCount_eq_sum _ _, fun A => run_chebyshevDensityProgram A k hk S δ G⟩

end NLAlib
