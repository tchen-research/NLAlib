import NLAlib.Matrix.FiniteIndexTransport

/-!
# Von Neumann-type trace inequalities

* `frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le`: the rank corollary of the von Neumann
  trace inequality, `⟨X, E⟩_F ≤ √r ‖X‖_F ‖E‖₂` when `rank X ≤ r`. This is the deterministic
  hypothesis `hVN` (`VonNeumannRankBound`) of the Chen–Persson LRA formalization; it is proved
  here directly through the range projector `X X⁺`, without the full trace inequality.

* `frobInner_le_sum_singularValues_mul`: the von Neumann trace inequality
  `⟨X, E⟩_F ≤ ∑ₖ σ_k(X) σ_k(E)`, through Ky Fan's maximum principle and Abel summation.

Audit G0 C4, A2. Atlas: `von-neumann-trace` (rank corollary and full inequality).
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Rank corollary of the von Neumann trace inequality.** If `rank X ≤ r` then
`⟨X, E⟩_F ≤ √r ‖X‖_F ‖E‖₂`. Proof: with the orthogonal projector `P = X X⁺` onto `range X`,
`⟨X, E⟩_F = ⟨X, P E⟩_F ≤ ‖X‖_F ‖P E‖_F ≤ ‖X‖_F √(rank P E) ‖P E‖₂ ≤ √r ‖X‖_F ‖E‖₂`.
It follows from Horn–Johnson 2013, Thm 7.4.1.1 (von Neumann) and Cauchy–Schwarz over the top
`r` singular values; this is the `VonNeumannRankBound` hypothesis of the Chen–Persson LRA
formalization. Audit G0 C4; atlas `von-neumann-trace` (rank corollary). Deviation: arbitrary
finite index types, no full-rank or nonemptiness condition. -/
theorem frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le {r : ℕ} (X E : Matrix m n ℝ)
    (hX : X.rank ≤ r) : frobInner X E ≤ Real.sqrt r * frobNorm X * specNorm E := by
  set P : Matrix m m ℝ := X * moorePenroseInverse X with hPdef
  have hPX : P * X = X := mul_moorePenroseInverse_mul X
  have hs : P.IsSymm := mul_moorePenroseInverse_isSymm X
  have hp : IsIdempotentElem P := mul_moorePenroseInverse_isIdempotentElem X
  have hinner : frobInner X E = frobInner X (P * E) := by
    have h := frobInner_mul_mul P X (1 : Matrix m m ℝ) E
    rw [hPX, Matrix.one_mul, Matrix.mul_one, hs.eq] at h
    exact h
  have hrank : ((P * E).rank : ℝ) ≤ r := by
    have h1 : (P * E).rank ≤ P.rank := Matrix.rank_mul_le_left P E
    have h2 : P.rank ≤ X.rank := Matrix.rank_mul_le_left X _
    exact_mod_cast h1.trans (h2.trans hX)
  have hspec : specNorm (P * E) ≤ specNorm E :=
    calc specNorm (P * E) ≤ specNorm P * specNorm E := specNorm_mul_le P E
      _ ≤ 1 * specNorm E :=
        mul_le_mul_of_nonneg_right (specNorm_le_one_of_isSymm_of_isIdempotentElem hs hp)
          (specNorm_nonneg E)
      _ = specNorm E := one_mul _
  have hfrob : frobNorm (P * E) ≤ Real.sqrt r * specNorm E :=
    calc frobNorm (P * E) ≤ Real.sqrt ((P * E).rank : ℝ) * specNorm (P * E) :=
          frobNorm_le_sqrt_rank_mul_specNorm_fintype (P * E)
      _ ≤ Real.sqrt r * specNorm E :=
          mul_le_mul (Real.sqrt_le_sqrt hrank) hspec (specNorm_nonneg _) (Real.sqrt_nonneg _)
  calc frobInner X E = frobInner X (P * E) := hinner
    _ ≤ frobNorm X * frobNorm (P * E) := frobInner_le_frobNorm_mul_frobNorm X (P * E)
    _ ≤ frobNorm X * (Real.sqrt r * specNorm E) :=
        mul_le_mul_of_nonneg_left hfrob (frobNorm_nonneg X)
    _ = Real.sqrt r * frobNorm X * specNorm E := by ring

/-! ### The von Neumann trace inequality -/

section TraceInequality

/-- Abel summation: partial-sum domination `∑_{i<k} dᵢ ≤ ∑_{i<k} tᵢ` (`k ≤ N`) survives
weighting by a nonnegative non-increasing sequence. -/
private theorem sum_range_mul_le_of_partial_le {s d t : ℕ → ℝ} {N : ℕ}
    (hs0 : ∀ i, 0 ≤ s i) (hs : Antitone s)
    (h : ∀ k ≤ N, ∑ i ∈ Finset.range k, d i ≤ ∑ i ∈ Finset.range k, t i) :
    ∑ i ∈ Finset.range N, s i * d i ≤ ∑ i ∈ Finset.range N, s i * t i := by
  set F : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, (t i - d i) with hF
  have hF0 : ∀ k ≤ N, 0 ≤ F k := fun k hk => by
    simp only [hF, Finset.sum_sub_distrib]
    linarith [h k hk]
  have key : ∀ K ≤ N, s K * F K ≤ ∑ i ∈ Finset.range K, s i * (t i - d i) := by
    intro K
    induction K with
    | zero => intro _; simp [hF]
    | succ K ih =>
      intro hK
      have ih' := ih (by omega)
      have hF1 := hF0 (K + 1) hK
      have hs1 : s (K + 1) ≤ s K := hs (Nat.le_succ K)
      have hFK : F (K + 1) = F K + (t K - d K) := by simp only [hF]; rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ, hFK]
      rw [hFK] at hF1
      nlinarith
  have hN := key N le_rfl
  have h0 : 0 ≤ s N * F N := mul_nonneg (hs0 N) (hF0 N le_rfl)
  have hsum : ∑ i ∈ Finset.range N, s i * (t i - d i) =
      ∑ i ∈ Finset.range N, s i * t i - ∑ i ∈ Finset.range N, s i * d i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- The diagonal of a rectangular matrix, as a zero-padded sequence. -/
private def diagSeq {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℝ) (i : ℕ) : ℝ :=
  if h : i < m ∧ i < n then D ⟨i, h.1⟩ ⟨i, h.2⟩ else 0

private theorem frobInner_rectDiag {m n : ℕ} (σ : ℕ → ℝ) (D : Matrix (Fin m) (Fin n) ℝ) :
    frobInner (rectDiag σ : Matrix (Fin m) (Fin n) ℝ) D =
      ∑ i ∈ Finset.range (min m n), σ i * diagSeq D i := by
  have h1 : frobInner (rectDiag σ : Matrix (Fin m) (Fin n) ℝ) D =
      ∑ i : Fin m, σ i * diagSeq D i := by
    unfold frobInner
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [rectDiag_apply, diagSeq]
    by_cases hi : (i : ℕ) < n
    · rw [Finset.sum_eq_single ⟨i, hi⟩]
      · simp [hi]
      · intro j _ hj
        rw [if_neg (fun h => hj (Fin.ext h.symm)), zero_mul]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [hi]
      · intro j _
        rw [if_neg (fun (h : (i : ℕ) = j) => hi (h ▸ j.isLt)), zero_mul]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => σ i * diagSeq D i) m]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    exact lt_of_lt_of_le hi (min_le_left m n)
  · intro i _ hi
    simp only [Finset.mem_range, lt_min_iff, not_and_or, not_lt] at hi
    have : ¬ (i < m ∧ i < n) := by omega
    simp [diagSeq, this]

private theorem sum_castLE_le {N M : ℕ} (h : N ≤ M) (f : Fin M → ℝ) (hf : ∀ j, 0 ≤ f j) :
    ∑ l : Fin N, f (Fin.castLE h l) ≤ ∑ j, f j := by
  rw [← Finset.sum_image (fun a _ b _ hab => Fin.castLE_injective h hab)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hf j)

private theorem sum_fin_ite_lt_eq_sum_range {N k : ℕ} (hk : k ≤ N) (g : ℕ → ℝ) :
    ∑ l : Fin N, (if (l : ℕ) < k then g l else 0) = ∑ i ∈ Finset.range k, g i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then g i else 0) N, ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

private theorem sum_sq_col_eq_one {m : ℕ} {P : Matrix (Fin m) (Fin m) ℝ} (hP : Pᵀ * P = 1)
    (c : Fin m) : ∑ j, P j c ^ 2 = 1 := by
  have := congrArg (fun M => M c c) hP
  simpa [Matrix.mul_apply, sq] using this

private theorem sum_sq_row_eq_one {m : ℕ} {P : Matrix (Fin m) (Fin m) ℝ} (hP : P * Pᵀ = 1)
    (c : Fin m) : ∑ j, P c j ^ 2 = 1 := by
  have := congrArg (fun M => M c c) hP
  simpa [Matrix.mul_apply, sq] using this

/-- **Ky Fan's maximum principle, diagonal form.** The sum of the first `k` diagonal entries of
`D` is at most the sum of its `k` largest singular values. -/
private theorem sum_range_diagSeq_le {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (hk : k ≤ min m n) :
    ∑ i ∈ Finset.range k, diagSeq D i ≤ ∑ i ∈ Finset.range k, singularValues D i := by
  obtain ⟨P, R, h⟩ := exists_isSVD D
  have hkm : k ≤ m := hk.trans (min_le_left m n)
  have hkn : k ≤ n := hk.trans (min_le_right m n)
  let p : ℕ → Fin (min m n) → ℝ := fun i l =>
    if hi : i < m then P ⟨i, hi⟩ (Fin.castLE (min_le_left m n) l) else 0
  let r : ℕ → Fin (min m n) → ℝ := fun i l =>
    if hi : i < n then R ⟨i, hi⟩ (Fin.castLE (min_le_right m n) l) else 0
  let t : Fin (min m n) → ℝ := fun l => singularValues D l
  have hdiag : ∀ i, diagSeq D i = ∑ l, t l * (p i l * r i l) := by
    intro i
    by_cases hi : i < m ∧ i < n
    · simp only [diagSeq, dif_pos hi, p, r, dif_pos hi.1, dif_pos hi.2, t]
      rw [h.apply]
      exact Finset.sum_congr rfl fun l _ => by ring
    · simp only [diagSeq, dif_neg hi]
      symm
      refine Finset.sum_eq_zero fun l _ => ?_
      rcases not_and_or.1 hi with h1 | h1 <;> simp [p, r, h1]
  have hcol : ∀ l, ∑ i ∈ Finset.range k, p i l ^ 2 ≤ 1 ∧
      ∑ i ∈ Finset.range k, r i l ^ 2 ≤ 1 := by
    intro l
    constructor
    · calc ∑ i ∈ Finset.range k, p i l ^ 2 ≤ ∑ i ∈ Finset.range m, p i l ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hkm)
              (fun _ _ _ => sq_nonneg _)
        _ = ∑ j : Fin m, P j (Fin.castLE (min_le_left m n) l) ^ 2 := by
            rw [← Fin.sum_univ_eq_sum_range (fun i => p i l ^ 2) m]
            simp [p]
        _ = 1 := sum_sq_col_eq_one h.transpose_mul_left _
    · calc ∑ i ∈ Finset.range k, r i l ^ 2 ≤ ∑ i ∈ Finset.range n, r i l ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hkn)
              (fun _ _ _ => sq_nonneg _)
        _ = ∑ j : Fin n, R j (Fin.castLE (min_le_right m n) l) ^ 2 := by
            rw [← Fin.sum_univ_eq_sum_range (fun i => r i l ^ 2) n]
            simp [r]
        _ = 1 := sum_sq_col_eq_one h.transpose_mul_right _
  have hrow : ∀ i, ∑ l, p i l ^ 2 ≤ 1 ∧ ∑ l, r i l ^ 2 ≤ 1 := by
    intro i
    constructor
    · by_cases hi : i < m
      · calc ∑ l, p i l ^ 2 = ∑ l : Fin (min m n),
              (fun j => P ⟨i, hi⟩ j ^ 2) (Fin.castLE (min_le_left m n) l) := by simp [p, hi]
          _ ≤ ∑ j, P ⟨i, hi⟩ j ^ 2 := sum_castLE_le _ _ fun _ => sq_nonneg _
          _ = 1 := sum_sq_row_eq_one h.mul_transpose_left _
      · simp [p, hi]
    · by_cases hi : i < n
      · calc ∑ l, r i l ^ 2 = ∑ l : Fin (min m n),
              (fun j => R ⟨i, hi⟩ j ^ 2) (Fin.castLE (min_le_right m n) l) := by simp [r, hi]
          _ ≤ ∑ j, R ⟨i, hi⟩ j ^ 2 := sum_castLE_le _ _ fun _ => sq_nonneg _
          _ = 1 := sum_sq_row_eq_one h.mul_transpose_right _
      · simp [r, hi]
  let w : Fin (min m n) → ℝ := fun l => ∑ i ∈ Finset.range k, (p i l ^ 2 + r i l ^ 2) / 2
  have hw0 : ∀ l, 0 ≤ w l := fun l =>
    Finset.sum_nonneg fun i _ => by positivity
  have hw1 : ∀ l, w l ≤ 1 := fun l => by
    have h1 := (hcol l).1
    have h2 := (hcol l).2
    simp only [w, ← Finset.sum_div, Finset.sum_add_distrib]
    linarith
  have hbudget : ∑ l, w l ≤ (k : ℝ) := by
    simp only [w]
    rw [Finset.sum_comm]
    calc ∑ i ∈ Finset.range k, ∑ l, (p i l ^ 2 + r i l ^ 2) / 2
        ≤ ∑ _i ∈ Finset.range k, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          have h1 := (hrow i).1
          have h2 := (hrow i).2
          rw [← Finset.sum_div, Finset.sum_add_distrib]
          linarith
      _ = k := by simp
  have hanti : Antitone t := fun a b hab =>
    singularValues_antitone D (show (a : ℕ) ≤ b from hab)
  calc ∑ i ∈ Finset.range k, diagSeq D i
      = ∑ l, t l * ∑ i ∈ Finset.range k, p i l * r i l := by
        simp_rw [hdiag, Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ l, t l * w l := Finset.sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (p i l - r i l)])
          (singularValues_nonneg D _)
    _ ≤ ∑ l : Fin (min m n), if (l : ℕ) < k then t l else 0 :=
        sum_mul_le_sum_ite_lt_of_antitone t w (fun l => singularValues_nonneg D _) hanti
          hw0 hw1 hbudget
    _ = ∑ i ∈ Finset.range k, singularValues D i :=
        sum_fin_ite_lt_eq_sum_range hk (singularValues D)

/-- **Von Neumann trace inequality.** For real `m × n` matrices,
`⟨X, E⟩_F = tr(XᵀE) ≤ ∑_{k < min m n} σ_k(X) σ_k(E)`. Horn–Johnson 2013, Thm 7.4.1.1 (real case,
`Re tr(X E*) = frobInner X E`); Mirsky 1975. Proof: Ky Fan's maximum principle for the diagonal
of `UᵀEV` (through the weighted top-`k` inequality `sum_mul_le_sum_ite_lt_of_antitone`) and
Abel summation over `σ(X)`; no Birkhoff theorem is needed. Audit G0 A2;
atlas `von-neumann-trace`. -/
theorem frobInner_le_sum_singularValues_mul {m n : ℕ} (X E : Matrix (Fin m) (Fin n) ℝ) :
    frobInner X E ≤ ∑ k ∈ Finset.range (min m n), singularValues X k * singularValues E k := by
  obtain ⟨U, V, h⟩ := exists_isSVD X
  set D : Matrix (Fin m) (Fin n) ℝ := Uᵀ * E * V with hDdef
  have hD : singularValues D = singularValues E := by
    have hU : (Uᵀ)ᵀ * Uᵀ = 1 := by rw [Matrix.transpose_transpose]; exact h.mul_transpose_left
    rw [hDdef, singularValues_mul_orthogonal _ h.transpose_mul_right,
      singularValues_orthogonal_mul _ hU]
  have hinner : frobInner X E =
      frobInner (rectDiag (singularValues X) : Matrix (Fin m) (Fin n) ℝ) D := by
    rw [frobInner_eq_trace, frobInner_eq_trace]
    conv_lhs => rw [h.eq]
    simp only [hDdef, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm V]
    simp only [Matrix.mul_assoc]
  rw [hinner, frobInner_rectDiag]
  refine sum_range_mul_le_of_partial_le (singularValues_nonneg X) (singularValues_antitone X)
    fun k hk => ?_
  rw [← hD]
  exact sum_range_diagSeq_le D hk

end TraceInequality

end NLAlib
