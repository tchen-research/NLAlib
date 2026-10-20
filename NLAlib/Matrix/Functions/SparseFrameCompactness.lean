import Mathlib.Data.Set.Card
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.Pigeonhole
import NLAlib.Matrix.Basic.PositiveSemidefiniteSeries

/-!
# Compactness and block extraction for sparse frame reweightings

Nonnegative reweightings with a fixed support budget are closed under limits of
their spectral sandwich constant. Boundedness of the weights is derived from
the upper matrix inequality after discarding zero vectors. A separate finite
block extraction theorem uses a support pigeonhole argument and principal
submatrices to retain the same spectral bounds on one block.

These elementary results support the passage from integer iteration budgets
to the real parameter in Batson--Spielman--Srivastava,
*Twice-Ramanujan Sparsifiers* (2008), Theorem 3.1
([arXiv:0808.0163](https://arxiv.org/abs/0808.0163)).
They do not depend on the barrier iteration theorem.
-/

noncomputable section
open scoped Matrix BigOperators MatrixOrder
open Filter Topology

namespace NLAlib

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- **Compactness of sparse nonnegative reweightings.**

Let `v : I → n → ℝ` be any finite family of real vectors (no isotropy,
nonemptiness, or nonzero-vector assumption is needed). If for every
`m` there is a nonnegative weight family `s_m` with at most `k` supporting
indices such that the weighted Gram matrix satisfies

`1 ≤ ∑ i, s_m i • v_i v_iᵀ ≤ beta m • 1`

and `beta m → b`, then there is one nonnegative weight family `s` with at
most `k` supporting indices such that

`1 ≤ ∑ i, s i • v_i v_iᵀ ≤ b • 1`.

This is the finite-dimensional closure of sparse nonnegative reweightings
under limits of the sandwich constant. -/
theorem exists_nonneg_weights_spectral_sandwich_of_tendsto
    (v : I → n → ℝ) (k : ℕ) (beta : ℕ → ℝ) (b : ℝ)
    (hbeta : Tendsto beta atTop (nhds b))
    (hseq : ∀ m, ∃ s : I → ℝ,
      (∀ i, 0 ≤ s i) ∧ (Function.support s).ncard ≤ k ∧
      ((1 : Matrix n n ℝ) ≤ ∑ i, s i • Matrix.vecMulVec (v i) (v i)) ∧
      (∑ i, s i • Matrix.vecMulVec (v i) (v i) ≤ beta m • (1 : Matrix n n ℝ))) :
    ∃ s : I → ℝ,
      (∀ i, 0 ≤ s i) ∧ (Function.support s).ncard ≤ k ∧
      ((1 : Matrix n n ℝ) ≤ ∑ i, s i • Matrix.vecMulVec (v i) (v i)) ∧
      (∑ i, s i • Matrix.vecMulVec (v i) (v i) ≤ b • (1 : Matrix n n ℝ)) := by
  classical
  let A : (I → ℝ) → Matrix n n ℝ := fun s => ∑ i, s i • Matrix.vecMulVec (v i) (v i)
  choose S₀ hS₀ using hseq
  let T : ℕ → I → ℝ := fun m i => if v i = 0 then 0 else S₀ m i
  have hS₀₂ : ∀ m, ∀ i, 0 ≤ S₀ m i := fun m => (hS₀ m).1
  have hS₀_card : ∀ m, (Function.support (S₀ m)).ncard ≤ k := fun m => (hS₀ m).2.1
  have hS₀_lower : ∀ m, (1 : Matrix n n ℝ) ≤ A (S₀ m) := fun m => (hS₀ m).2.2.1
  have hS₀_upper : ∀ m, A (S₀ m) ≤ beta m • (1 : Matrix n n ℝ) := fun m => (hS₀ m).2.2.2
  have hT_nonneg : ∀ m i, 0 ≤ T m i := by
    intro m i
    dsimp [T]
    by_cases hvi : v i = 0
    · simp [hvi]
    · simp [hvi, hS₀₂ m i]
  have hT_support : ∀ m, Function.support (T m) ⊆ Function.support (S₀ m) := by
    intro m i hi
    dsimp [T] at hi
    by_cases hvi : v i = 0
    · simp [hvi] at hi
    · simpa [hvi] using hi
  have hT_eqA : ∀ m, A (T m) = A (S₀ m) := by
    intro m
    unfold A
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hvi : v i = 0
    · simp [T, hvi]
    · simp [T, hvi]
  have hT_lower : ∀ m, (1 : Matrix n n ℝ) ≤ A (T m) := by
    intro m
    rw [hT_eqA]
    exact hS₀_lower m
  have hT_upper : ∀ m, A (T m) ≤ beta m • (1 : Matrix n n ℝ) := by
    intro m
    rw [hT_eqA]
    exact hS₀_upper m
  -- diagonal identity of the weighted Gram matrix
  have hA_diag : ∀ m j, A (T m) j j = ∑ i, T m i * (v i j)^2 := by
    intro m j
    dsimp [A]
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, pow_two]
  -- beta is bounded above; replace the bound by max K₀ 0 ≥ 0.
  have hbdd : ∃ a, a ∈ upperBounds (Set.range beta) := hbeta.bddAbove_range
  obtain ⟨K₀, hK₀⟩ := hbdd
  let K : ℝ := max K₀ 0
  have hbeta_le_K : ∀ m, beta m ≤ K := by
    intro m
    exact (hK₀ ⟨m, rfl⟩).trans (le_max_left _ _)
  have hK_nonneg : 0 ≤ K := le_max_right _ _
  -- choose a witness coordinate for each nonzero vector
  have hcoords : ∀ i, v i ≠ 0 → ∃ j : n, v i j ≠ 0 := by
    intro i hvi
    by_contra hnot
    apply hvi
    funext j
    by_contra hj
    exact hnot ⟨j, hj⟩
  let c : I → ℝ := fun i =>
    if h : v i = 0 then 0 else K / (v i (Classical.choose (hcoords i h)))^2
  have hT_le_c : ∀ m i, T m i ≤ c i := by
    intro m i
    dsimp [T, c]
    by_cases hvi : v i = 0
    · simp [hvi]
    · let j₀ : n := Classical.choose (hcoords i hvi)
      have hvi₀ : v i j₀ ≠ 0 := Classical.choose_spec (hcoords i hvi)
      have hPSD_upper : ∀ m, (beta m • (1 : Matrix n n ℝ) - A (T m)).PosSemidef := by
        intro m
        rw [← Matrix.le_iff]
        exact hT_upper m
      have hdiag : ∀ m, ∑ i, T m i * (v i j₀)^2 ≤ beta m := by
        intro m
        have hnonneg : 0 ≤ (beta m • (1 : Matrix n n ℝ) - A (T m)) j₀ j₀ :=
          (hPSD_upper m).diag_nonneg
        have h1 : (beta m • (1 : Matrix n n ℝ)) j₀ j₀ = beta m := by simp
        have hnonneg' : 0 ≤ beta m - (∑ i, T m i * (v i j₀)^2) := by
          rw [Matrix.sub_apply] at hnonneg
          simpa [h1, hA_diag m j₀] using hnonneg
        linarith
      have hterm : ∀ m, T m i * (v i j₀)^2 ≤ ∑ l, T m l * (v l j₀)^2 := by
        intro m
        have hnonneg_terms : ∀ l ∈ (Finset.univ : Finset I), 0 ≤ T m l * (v l j₀)^2 := by
          intro l hl
          exact mul_nonneg (hT_nonneg m l) (sq_nonneg _)
        have hsingle := Finset.single_le_sum hnonneg_terms (Finset.mem_univ i)
        simpa using hsingle
      have hTi_le : ∀ m, S₀ m i ≤ K / (v i j₀)^2 := by
        intro m
        have hpos : 0 < (v i j₀)^2 := sq_pos_of_ne_zero hvi₀
        have hle : S₀ m i * (v i j₀)^2 ≤ K := by
          have hTid : T m i = S₀ m i := by simp [T, hvi]
          rw [← hTid]
          exact le_trans (le_trans (hterm m) (hdiag m)) (hbeta_le_K m)
        exact (le_div_iff₀ hpos).2 hle
      simpa [T, c, hvi, j₀] using hTi_le m
  have hbox : ∀ m, T m ∈ Set.Icc (0 : I → ℝ) c := by
    intro m
    exact ⟨fun i => hT_nonneg m i, fun i => hT_le_c m i⟩
  have hbox_compact : IsCompact (Set.Icc (0 : I → ℝ) c) := isCompact_Icc
  obtain ⟨t, ht_in, phi, hphi_mono, hphi_tendsto⟩ :=
    IsCompact.tendsto_subseq hbox_compact hbox
  have ht_nonneg : ∀ i, 0 ≤ t i := fun i => (ht_in.1 i)
  -- support cannot grow beyond k in the limit
  have hcoord_conv : ∀ i, Tendsto (fun m => T (phi m) i) atTop (nhds (t i)) := by
    intro i
    exact (continuous_apply i).continuousAt.tendsto.comp hphi_tendsto
  have hnev : ∀ i, t i ≠ 0 → ∀ᶠ m in atTop, T (phi m) i ≠ 0 := by
    intro i hti
    exact (hcoord_conv i).eventually_ne hti
  have hfall : ∀ᶠ m in atTop, ∀ i, t i ≠ 0 → T (phi m) i ≠ 0 := by
    rw [eventually_all]
    intro i
    by_cases hti : t i ≠ 0
    · exact (hnev i hti).mono (fun m hm _ => hm)
    · exact Eventually.of_forall (fun m hi => False.elim (hti hi))
  obtain ⟨m, hm⟩ := hfall.exists
  have hsup : Function.support t ⊆ Function.support (T (phi m)) := by
    intro i hi
    exact hm i hi
  have hcard : (Function.support t).ncard ≤ k := by
    calc
      (Function.support t).ncard ≤ (Function.support (T (phi m))).ncard := Set.ncard_mono hsup
      _ ≤ (Function.support (S₀ (phi m))).ncard := Set.ncard_mono (hT_support (phi m))
      _ ≤ k := hS₀_card (phi m)
  -- continuity of the weighted Gram map
  have hcontA : Continuous A := by
    unfold A
    refine continuous_finsetSum (Finset.univ : Finset I) (fun i _ => ?_)
    exact (continuous_apply i).smul continuous_const
  have hphi_atTop : Tendsto phi atTop atTop := hphi_mono.tendsto_atTop
  -- lower Loewner inequality by passage to the limit
  have hL_psd : ∀ m, (A (T (phi m)) - (1 : Matrix n n ℝ)).PosSemidef := by
    intro m
    rw [← Matrix.le_iff]
    exact hT_lower (phi m)
  have hL_tendsto : Tendsto (fun m => A (T (phi m)) - (1 : Matrix n n ℝ)) atTop
      (nhds (A t - (1 : Matrix n n ℝ))) := by
    exact (hcontA.continuousAt.tendsto.comp hphi_tendsto).sub tendsto_const_nhds
  have hL_psd' : (A t - (1 : Matrix n n ℝ)).PosSemidef :=
    posSemidef_of_tendsto (l := atTop) hL_psd hL_tendsto
  have hLower : (1 : Matrix n n ℝ) ≤ A t := by
    rw [Matrix.le_iff]
    exact hL_psd'
  -- upper Loewner inequality by passage to the limit
  have hU_psd : ∀ m, (beta (phi m) • (1 : Matrix n n ℝ) - A (T (phi m))).PosSemidef := by
    intro m
    rw [← Matrix.le_iff]
    exact hT_upper (phi m)
  have hbeta_tendsto : Tendsto (fun m => beta (phi m)) atTop (nhds b) :=
    hbeta.comp hphi_atTop
  have hU_tendsto : Tendsto (fun m => beta (phi m) • (1 : Matrix n n ℝ) - A (T (phi m))) atTop
      (nhds (b • (1 : Matrix n n ℝ) - A t)) := by
    exact (hbeta_tendsto.smul tendsto_const_nhds).sub (hcontA.continuousAt.tendsto.comp hphi_tendsto)
  have hU_psd' : (b • (1 : Matrix n n ℝ) - A t).PosSemidef :=
    posSemidef_of_tendsto (l := atTop) hU_psd hU_tendsto
  have hUpper : A t ≤ b • (1 : Matrix n n ℝ) := by
    rw [Matrix.le_iff]
    exact hU_psd'
  refine ⟨t, ht_nonneg, hcard, ?_, ?_⟩
  · simpa [A] using hLower
  · simpa [A] using hUpper

/-- Unscaled copy of the frame on a product dimension: atom `(i,a)` becomes the
vector on `n × Fin r` that equals `v i` on block `a` and vanishes outside it.
This is the block lifting used by
`exists_nonneg_weights_spectral_sandwich_of_block_sum`. -/
def frameBlockVector {I n : Type*} (v : I → n → ℝ) (r : ℕ) (p : I × Fin r) :
    n × Fin r → ℝ :=
  fun x => if p.2 = x.2 then v p.1 x.1 else 0

omit [Fintype n] [DecidableEq n] in
/-- The matrix identity underlying block extraction: for every real coefficient
family `w` on `I × Fin r`, the weighted Gram sum of the lifted vectors is
exactly the block diagonal whose block `a` is the weighted Gram sum of the
original atoms restricted to fiber `a`. -/
lemma sum_smul_vecMulVec_frameBlockVector_eq_blockDiagonal (v : I → n → ℝ) (r : ℕ)
    (w : I × Fin r → ℝ) :
    (∑ p : I × Fin r, w p • Matrix.vecMulVec (frameBlockVector v r p) (frameBlockVector v r p))
      = Matrix.blockDiagonal (fun a : Fin r =>
          ∑ i : I, w (i, a) • Matrix.vecMulVec (v i) (v i)) := by
  classical
  ext ⟨x, a⟩ ⟨y, b⟩
  rw [Matrix.blockDiagonal_apply]
  by_cases hab : a = b
  · subst b
    simp only [frameBlockVector, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul]
    have hcond : ∀ p : I × Fin r,
        w p * ((if p.2 = a then v p.1 x else 0) * (if p.2 = a then v p.1 y else 0))
          = if p.2 = a then w p * (v p.1 x * v p.1 y) else 0 := by
      intro p
      by_cases hp : p.2 = a
      · simp [hp]
      · simp [hp]
    have himg : (Finset.univ : Finset I).image (fun i : I => (i, a))
        = (Finset.univ : Finset (I × Fin r)).filter (fun p => p.2 = a) := by
      ext p
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩
        exact (congrArg Prod.snd hi).symm
      · intro hp
        refine ⟨p.1, ?_⟩
        ext <;> simp [hp]
    have himj : Set.InjOn (fun i : I => (i, a)) (↑(Finset.univ : Finset I)) := by
      intro i hi j hj hij
      exact congrArg Prod.fst hij
    have hmap' : (∑ p ∈ (Finset.univ : Finset I).image (fun i : I => (i, a)),
        w p * (v p.1 x * v p.1 y))
        = ∑ i ∈ (Finset.univ : Finset I), w (i, a) * (v i x * v i y) :=
      Finset.sum_image himj
    calc
      (∑ p : I × Fin r, w p * ((if p.2 = a then v p.1 x else 0) * (if p.2 = a then v p.1 y else 0)))
          = ∑ p : I × Fin r, (if p.2 = a then w p * (v p.1 x * v p.1 y) else 0) := by
              exact Finset.sum_congr rfl (fun p _ => hcond p)
      _ = (∑ p ∈ (Finset.univ : Finset (I × Fin r)).filter (fun p => p.2 = a),
            w p * (v p.1 x * v p.1 y)) := by
              rw [Finset.sum_filter]
      _ = ∑ i : I, w (i, a) * (v i x * v i y) := by
              rw [← himg]
              exact hmap'.trans (by simp)
  · simp only [frameBlockVector, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul]
    have hsum : (∑ p : I × Fin r,
        w p * ((if p.2 = a then v p.1 x else 0) * (if p.2 = b then v p.1 y else 0))) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      by_cases hpa : p.2 = a
      · have hpb : p.2 ≠ b := by
          intro hb
          exact hab (hpa.symm.trans hb)
        rw [if_pos hpa, if_neg hpb]
        ring
      · rw [if_neg hpa]
        ring
    simpa [hab] using hsum

omit [Fintype n] in
/-- The unweighted lifted frame of an isotropic frame is again isotropic: if
`∑ i, v_i v_iᵀ = 1`, then `∑ p, V_p V_pᵀ = 1` for the unscaled block lift
`V = frameBlockVector v r`. -/
lemma sum_vecMulVec_frameBlockVector_eq_one (v : I → n → ℝ) (r : ℕ)
    (hframe : ∑ i, Matrix.vecMulVec (v i) (v i) = 1) :
    ∑ p : I × Fin r, Matrix.vecMulVec (frameBlockVector v r p) (frameBlockVector v r p) = 1 := by
  classical
  have h' : (∑ p : I × Fin r,
      (1 : ℝ) • Matrix.vecMulVec (frameBlockVector v r p) (frameBlockVector v r p)) = 1 := by
    rw [sum_smul_vecMulVec_frameBlockVector_eq_blockDiagonal v r (fun _ : I × Fin r => 1)]
    ext ⟨x, a⟩ ⟨y, b⟩
    rw [Matrix.blockDiagonal_apply]
    by_cases hab : a = b
    · subst b
      have he := congr_fun (congr_fun hframe x) y
      simpa [Matrix.one_apply, one_smul] using he
    · have hz : (∑ p : I × Fin r,
          Matrix.vecMulVec (frameBlockVector v r p) (frameBlockVector v r p)) (x, a) (y, b) = 0 := by
        rw [Matrix.sum_apply]
        simp only [frameBlockVector, Matrix.vecMulVec_apply]
        apply Finset.sum_eq_zero
        intro p hp
        by_cases hpa : p.2 = a
        · have hpb : p.2 ≠ b := by
            intro hb
            exact hab (hpa.symm.trans hb)
          rw [if_pos hpa, if_neg hpb]
          ring
        · rw [if_neg hpa]
          ring
      simp [hab] at *
  simpa using h'

omit [Fintype n] in
/-- **Finite block extraction.**

Let `w : I × Fin r → ℝ` be nonnegative with total support strictly below
`r*(k+1)`, and assume the weighted Gram sum of the unscaled lifted frame lies
between `1` and `B • 1`.  Then some principal block `a₀` gives an
original-dimensional weight family `s i = w (i, a₀)` with support at most `k`
whose Gram sum lies between `1` and `B • 1`. -/
theorem exists_nonneg_weights_spectral_sandwich_of_block_sum
    (v : I → n → ℝ) (r : ℕ) (_hr : 0 < r) (k : ℕ) (B : ℝ)
    (w : I × Fin r → ℝ)
    (hw_nonneg : ∀ p, 0 ≤ w p)
    (hw_card : (Function.support w).ncard < r * (k + 1))
    (hw_lower : (1 : Matrix (n × Fin r) (n × Fin r) ℝ) ≤
        ∑ p, w p • Matrix.vecMulVec (frameBlockVector v r p) (frameBlockVector v r p))
    (hw_upper : (∑ p, w p • Matrix.vecMulVec (frameBlockVector v r p) (frameBlockVector v r p)) ≤
        B • (1 : Matrix (n × Fin r) (n × Fin r) ℝ)) :
    ∃ s : I → ℝ,
      (∀ i, 0 ≤ s i) ∧ (Function.support s).ncard ≤ k ∧
      ((1 : Matrix n n ℝ) ≤ ∑ i, s i • Matrix.vecMulVec (v i) (v i)) ∧
      (∑ i, s i • Matrix.vecMulVec (v i) (v i) ≤ B • (1 : Matrix n n ℝ)) := by
  classical
  let S : Finset (I × Fin r) := (Finset.univ.filter fun p => w p ≠ 0)
  have hmem_S : ∀ p, p ∈ S ↔ w p ≠ 0 := by
    intro p
    simp [S]
  have hS_card : S.card < (Finset.univ : Finset (Fin r)).card * (k + 1) := by
    have hw : (Function.support w).ncard = S.card := by
      dsimp [S]
      rw [Set.ncard_eq_toFinset_card]
      congr 1
      ext p
      simp [Function.support]
    rw [← hw]
    simpa [Fintype.card_fin]
  obtain ⟨a₀, -, hfiber⟩ :=
    Finset.exists_card_fiber_lt_of_card_lt_mul
      (s := S) (t := (Finset.univ : Finset (Fin r)))
      (f := fun p : I × Fin r => p.2) (n := k + 1) hS_card
  have hfib_card : (S.filter fun p => p.2 = a₀).card < k + 1 := hfiber
  have hfib_ncard : {p : I × Fin r | p ∈ S ∧ p.2 = a₀}.ncard < k + 1 := by
    have hc : {p : I × Fin r | p ∈ S ∧ p.2 = a₀}.ncard = (S.filter fun p => p.2 = a₀).card := by
      rw [Set.ncard_eq_toFinset_card]
      congr 1
      ext p
      simp
    rwa [hc]
  have hfib_set : {p : I × Fin r | p ∈ S ∧ p.2 = a₀}
      = (fun i : I => (i, a₀)) '' (Function.support fun i => w (i, a₀)) := by
    ext p
    constructor
    · rintro ⟨hpS, h₂⟩
      have hw : w p ≠ 0 := (hmem_S p).1 hpS
      refine ⟨p.1, ?_, ?_⟩
      · have hpair : (p.1, a₀) = p := by ext <;> simp [h₂]
        simpa [hpair] using hw
      · ext <;> simp [h₂]
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(hmem_S (i, a₀)).2 hi, rfl⟩
  have hinj : Function.Injective (fun i : I => (i, a₀)) := by
    intro i j h
    exact congrArg Prod.fst h
  have hcard_block : (Function.support fun i => w (i, a₀)).ncard ≤ k := by
    have hcard_eq : (Function.support fun i => w (i, a₀)).ncard
        = {p : I × Fin r | p ∈ S ∧ p.2 = a₀}.ncard := by
      rw [hfib_set]
      exact (Set.ncard_image_of_injective (Function.support fun i => w (i, a₀)) hinj).symm
    have hlt : (Function.support fun i => w (i, a₀)).ncard < k + 1 := by
      rwa [hcard_eq]
    exact Nat.le_of_lt_succ hlt
  let V : I × Fin r → n × Fin r → ℝ := fun p => frameBlockVector v r p
  let A : (I × Fin r → ℝ) → Matrix (n × Fin r) (n × Fin r) ℝ :=
    fun w => ∑ p, w p • Matrix.vecMulVec (V p) (V p)
  let e : n → n × Fin r := fun j => (j, a₀)
  have hinj_e : Function.Injective e := by
    intro j₁ j₂ h
    exact congrArg Prod.fst h
  have hPSD_low : ((A w - (1 : Matrix (n × Fin r) (n × Fin r) ℝ)).submatrix e e).PosSemidef := by
    have hPSD : (A w - (1 : Matrix (n × Fin r) (n × Fin r) ℝ)).PosSemidef := by
      rw [← Matrix.le_iff]
      exact hw_lower
    exact hPSD.submatrix e
  have hsub_1 : ((1 : Matrix (n × Fin r) (n × Fin r) ℝ).submatrix e e) = 1 := by
    exact Matrix.submatrix_one e hinj_e
  have hsub_A : (A w).submatrix e e = ∑ i, w (i, a₀) • Matrix.vecMulVec (v i) (v i) := by
    dsimp [A, V]
    rw [sum_smul_vecMulVec_frameBlockVector_eq_blockDiagonal v r w]
    ext i j
    rw [Matrix.submatrix_apply, Matrix.blockDiagonal_apply_eq]
  have h1_e : ∀ i j, (1 : Matrix (n × Fin r) (n × Fin r) ℝ) (e i) (e j)
      = (1 : Matrix n n ℝ) i j := by
    intro i j
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · have hne : e i ≠ e j := by
        intro h
        exact hij (congrArg Prod.fst h)
      simp [hne, hij]
  have hsub_B : (B • (1 : Matrix (n × Fin r) (n × Fin r) ℝ)).submatrix e e = B • (1 : Matrix n n ℝ) := by
    ext i j
    rw [Matrix.submatrix_apply]
    rw [Matrix.smul_apply, Matrix.smul_apply]
    rw [h1_e]
  have hsub_diff : ((A w - (1 : Matrix (n × Fin r) (n × Fin r) ℝ)).submatrix e e)
      = (∑ i, w (i, a₀) • Matrix.vecMulVec (v i) (v i)) - (1 : Matrix n n ℝ) := by
    ext i j
    change A w (e i) (e j) - (1 : Matrix (n × Fin r) (n × Fin r) ℝ) (e i) (e j)
      = (∑ i, w (i, a₀) • Matrix.vecMulVec (v i) (v i)) i j - (1 : Matrix n n ℝ) i j
    have hiA : A w (e i) (e j) = (∑ i, w (i, a₀) • Matrix.vecMulVec (v i) (v i)) i j := by
      simpa [Matrix.submatrix_apply] using congr_fun (congr_fun hsub_A i) j
    have hi1 : (1 : Matrix (n × Fin r) (n × Fin r) ℝ) (e i) (e j) = (1 : Matrix n n ℝ) i j := by
      have h := congr_fun (congr_fun hsub_1 i) j
      simpa [Matrix.submatrix_apply] using h
    rw [hiA, hi1]
  have hblock_psd : ((∑ i, w (i, a₀) • Matrix.vecMulVec (v i) (v i)) - (1 : Matrix n n ℝ)).PosSemidef := by
    simpa only [hsub_diff] using hPSD_low
  have hblock_lower : (1 : Matrix n n ℝ) ≤ ∑ i, w (i, a₀) • Matrix.vecMulVec (v i) (v i) := by
    rw [Matrix.le_iff]
    exact hblock_psd
  have hPSD_up : (B • (1 : Matrix (n × Fin r) (n × Fin r) ℝ) - A w).PosSemidef := by
    rw [← Matrix.le_iff]
    exact hw_upper
  have hPSD_up_sub : ((B • (1 : Matrix (n × Fin r) (n × Fin r) ℝ) - A w).submatrix e e).PosSemidef :=
    hPSD_up.submatrix e
  have hsub_updiff : ((B • (1 : Matrix (n × Fin r) (n × Fin r) ℝ) - A w).submatrix e e)
      = B • (1 : Matrix n n ℝ) - (∑ i, w (i, a₀) • Matrix.vecMulVec (v i) (v i)) := by
    ext i j
    change (B • (1 : Matrix (n × Fin r) (n × Fin r) ℝ)) (e i) (e j) - A w (e i) (e j)
      = (B • (1 : Matrix n n ℝ)) i j - (∑ i, w (i, a₀) • Matrix.vecMulVec (v i) (v i)) i j
    have hiB : (B • (1 : Matrix (n × Fin r) (n × Fin r) ℝ)) (e i) (e j) = (B • (1 : Matrix n n ℝ)) i j := by
      have h := congr_fun (congr_fun hsub_B i) j
      simpa [Matrix.submatrix_apply] using h
    have hiA : A w (e i) (e j) = (∑ i, w (i, a₀) • Matrix.vecMulVec (v i) (v i)) i j := by
      simpa [Matrix.submatrix_apply] using congr_fun (congr_fun hsub_A i) j
    rw [hiB, hiA]
  have hblock_up_psd : (B • (1 : Matrix n n ℝ) - (∑ i, w (i, a₀) • Matrix.vecMulVec (v i) (v i))).PosSemidef := by
    simpa only [hsub_updiff] using hPSD_up_sub
  have hblock_upper : (∑ i, w (i, a₀) • Matrix.vecMulVec (v i) (v i)) ≤ B • (1 : Matrix n n ℝ) := by
    rw [Matrix.le_iff]
    exact hblock_up_psd
  refine ⟨fun i => w (i, a₀), ?_, hcard_block, hblock_lower, hblock_upper⟩
  exact fun i => hw_nonneg (i, a₀)

end NLAlib
