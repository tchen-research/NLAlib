import NLAlib.Matrix.Structured.GramianBalancing
/-!
# Exact Hankel SVD realization

Finite controllability and observability arrays factor the block Hankel
matrices. Their full-state thin SVD gives ERA coordinates similar to the
original realization, with the input/output selector formulas and every
Markov parameter preserved. The Hankel rank is a lower bound on every other
state realization with the same data.

Source: Brunton–Kutz (2022), §9.3; matrix-toolkit re-derivation, §63.
Atlas: `hankel-svd-era-realization`.
-/
noncomputable section
open Matrix
open scoped Matrix
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n p q : Type*} [Fintype n] [Fintype p] [Fintype q]
variable [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-- Finite observability array with `s` block rows, starting at power zero. -/
def observabilityArray (A : Matrix n n 𝕜) (C : Matrix p n 𝕜) (s : ℕ) :
    Matrix (Fin s × p) n 𝕜 := fun i j => (C * A ^ i.1.val) i.2 j

/-- Finite controllability array with `t` block columns, starting at power zero. -/
def controllabilityArray (A : Matrix n n 𝕜) (B : Matrix n q 𝕜) (t : ℕ) :
    Matrix n (Fin t × q) 𝕜 := fun i j => (A ^ j.1.val * B) i j.2

/-- A finite block Hankel matrix of Markov parameters with a time shift. -/
def blockHankel (A : Matrix n n 𝕜) (B : Matrix n q 𝕜) (C : Matrix p n 𝕜)
    (s t shift : ℕ) : Matrix (Fin s × p) (Fin t × q) 𝕜 :=
  fun i j => (C * A ^ (i.1.val + j.1.val + shift) * B) i.2 j.2

/-- The zeroth Hankel matrix is the observability/controllability product. -/
theorem blockHankel_zero_eq (A : Matrix n n 𝕜) (B : Matrix n q 𝕜) (C : Matrix p n 𝕜)
    (s t : ℕ) : blockHankel A B C s t 0 =
      observabilityArray A C s * controllabilityArray A B t := by
  ext i j
  change (C * A ^ (i.1.val + j.1.val + 0) * B) i.2 j.2 =
    ((C * A ^ i.1.val) * (A ^ j.1.val * B)) i.2 j.2
  simp only [Nat.add_zero, pow_add, Matrix.mul_assoc]

/-- The shifted Hankel matrix inserts exactly one state transition. -/
theorem blockHankel_one_eq (A : Matrix n n 𝕜) (B : Matrix n q 𝕜) (C : Matrix p n 𝕜)
    (s t : ℕ) : blockHankel A B C s t 1 =
      observabilityArray A C s * A * controllabilityArray A B t := by
  ext i j
  have hp : A ^ (i.1.val + j.1.val + 1) = A ^ i.1.val * A * A ^ j.1.val := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  change (C * A ^ (i.1.val + j.1.val + 1) * B) i.2 j.2 =
    (((C * A ^ i.1.val) * A) * (A ^ j.1.val * B)) i.2 j.2
  rw [hp]
  simp only [Matrix.mul_assoc]

/-- Injection into the first input block column. -/
def firstBlockInput (t : ℕ) (ht : 0 < t) : Matrix (Fin t × q) q 𝕜 :=
  fun i j => if i.1 = ⟨0, ht⟩ then (1 : Matrix q q 𝕜) i.2 j else 0

/-- Extraction of the first output block row. -/
def firstBlockOutput (s : ℕ) (hs : 0 < s) : Matrix p (Fin s × p) 𝕜 :=
  fun i j => if j.1 = ⟨0, hs⟩ then (1 : Matrix p p 𝕜) i j.2 else 0

/-- The first controllability block is the input matrix. -/
theorem controllabilityArray_mul_firstBlockInput (A : Matrix n n 𝕜) (B : Matrix n q 𝕜)
    (t : ℕ) (ht : 0 < t) : controllabilityArray A B t * firstBlockInput t ht = B := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_prod_type, firstBlockInput, controllabilityArray,
    Matrix.one_apply]

/-- The first observability block is the output matrix. -/
theorem firstBlockOutput_mul_observabilityArray (A : Matrix n n 𝕜) (C : Matrix p n 𝕜)
    (s : ℕ) (hs : 0 < s) : firstBlockOutput s hs * observabilityArray A C s = C := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_prod_type, firstBlockOutput, observabilityArray,
    Matrix.one_apply]

/-- The ERA state matrix from the shifted Hankel data. -/
def eraStateMatrix {u v : Type*} [Fintype u] [Fintype v]
    (H₁ : Matrix u v 𝕜) (U : Matrix u n 𝕜) (V : Matrix v n 𝕜) (σ : n → ℝ) :
    Matrix n n 𝕜 := invSqrtDiagonal σ * Uᴴ * H₁ * V * invSqrtDiagonal σ

/-- The ERA input matrix from the singular factors and first block selector. -/
def eraInputMatrix {v : Type*} [Fintype v]
    (V : Matrix v n 𝕜) (σ : n → ℝ) (E : Matrix v q 𝕜) : Matrix n q 𝕜 :=
  sqrtDiagonal σ * Vᴴ * E

/-- The ERA output matrix from the singular factors and first block selector. -/
def eraOutputMatrix {u : Type*} [Fintype u]
    (U : Matrix u n 𝕜) (σ : n → ℝ) (E : Matrix p u 𝕜) : Matrix p n 𝕜 :=
  E * U * sqrtDiagonal σ

/-- The exact full-state ERA formulas give an invertible state-coordinate
change and preserve the realization by similarity. The SVD is of the actual
block Hankel matrix; no pre-assumed realization certificate is used.
Brunton–Kutz (2022), §9.3.
atlas: hankel-svd-era-realization (partial) -/
theorem IsThinSVD.era_similarity {A : Matrix n n 𝕜} {B : Matrix n q 𝕜}
    {C : Matrix p n 𝕜} {s t : ℕ} (hs : 0 < s) (ht : 0 < t)
    {U : Matrix (Fin s × p) n 𝕜} {V : Matrix (Fin t × q) n 𝕜} {σ : n → ℝ}
    (h : IsThinSVD (blockHankel A B C s t 0) U V σ) :
    let T := balancingTrialMap (controllabilityArray A B t) V σ
    IsUnit T ∧
      eraStateMatrix (blockHankel A B C s t 1) U V σ = T⁻¹ * A * T ∧
      eraInputMatrix V σ (firstBlockInput t ht) = T⁻¹ * B ∧
      eraOutputMatrix U σ (firstBlockOutput s hs) = C * T := by
  let O := observabilityArray A C s
  let R := controllabilityArray A B t
  let D := invSqrtDiagonal (𝕜 := 𝕜) σ
  let S := diagonal (fun i => (σ i : 𝕜))
  have hh : IsThinSVD (O * R) U V σ := by
    simpa only [O, R, ← blockHankel_zero_eq] using h
  have hp := hh.isSingularTripletFamily
  obtain ⟨hunit, hinv, -, -, -⟩ := hp.full_gramian_balancing
  have hD : Dᴴ = D := invSqrtDiagonal_isHermitian σ
  have hinv' : (balancingTrialMap R V σ)⁻¹ = D * Uᴴ * O := by
    rw [hinv]
    simp only [balancingTestMap, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,
      (invSqrtDiagonal_isHermitian σ).eq, D, Matrix.mul_assoc]
  refine ⟨hunit, ?_, ?_, ?_⟩
  · rw [blockHankel_one_eq, hinv']
    simp only [eraStateMatrix, balancingTrialMap, O, R, D, Matrix.mul_assoc]
  · have hleft : Uᴴ * (O * R) = S * Vᴴ := by
      have hS : Sᴴ = S := by
        ext i j
        by_cases hij : i = j
        · subst j; simp [S, Matrix.conjTranspose_apply]
        · simp [S, Matrix.conjTranspose_apply, hij, Ne.symm hij]
      have he := congrArg Matrix.conjTranspose hp.adjoint_mul_left
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at he
      change Uᴴ * (O * R) = Sᴴ * Vᴴ at he
      rwa [hS] at he
    rw [hinv', ← controllabilityArray_mul_firstBlockInput A B t ht]
    change sqrtDiagonal σ * Vᴴ * firstBlockInput t ht =
      D * Uᴴ * O * (R * firstBlockInput t ht)
    calc
      _ = (D * S) * Vᴴ * firstBlockInput t ht := by
        rw [invSqrtDiagonal_mul_diagonal σ hh.pos]
      _ = _ := by rw [Matrix.mul_assoc D S Vᴴ, ← hleft]; simp only [Matrix.mul_assoc]
  · change firstBlockOutput s hs * U * sqrtDiagonal σ =
      C * (R * V * D)
    have hOT : O * (R * V * D) = U * sqrtDiagonal σ := by
      calc
        _ = ((O * R) * V) * D := by simp only [Matrix.mul_assoc]
        _ = (U * S) * D := by rw [hp.mul_right]
        _ = _ := by rw [Matrix.mul_assoc, diagonal_mul_invSqrtDiagonal σ hh.pos]
    rw [← firstBlockOutput_mul_observabilityArray A C s hs]
    change firstBlockOutput (p := p) s hs * U * sqrtDiagonal σ =
      firstBlockOutput (p := p) s hs * O * (R * V * D)
    rw [Matrix.mul_assoc (firstBlockOutput (p := p) s hs) O, hOT, Matrix.mul_assoc]

/-- Similar realizations have identical Markov parameters at every natural
time, with no stability or diagonalizability assumption. -/
theorem markovParameter_eq_of_similarity (A : Matrix n n 𝕜) (B : Matrix n q 𝕜)
    (C : Matrix p n 𝕜) {T : Matrix n n 𝕜} (hT : IsUnit T) (j : ℕ) :
    (C * T) * (T⁻¹ * A * T) ^ j * (T⁻¹ * B) = C * A ^ j * B := by
  have hl : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hT)
  have hr : T * T⁻¹ = 1 := mul_eq_one_comm.mp hl
  have hpow : ∀ j : ℕ, (T⁻¹ * A * T) ^ j = T⁻¹ * A ^ j * T := by
    intro k
    induction k with
    | zero => simp [hl]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc T T⁻¹, hr, Matrix.one_mul]
  rw [hpow]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc T T⁻¹, hr, Matrix.one_mul,
    ← Matrix.mul_assoc T T⁻¹, hr, Matrix.one_mul]

/-- Every state realization has Hankel rank at most its state dimension;
this supplies the ERA minimality obstruction for matching data. -/
theorem rank_blockHankel_le (A : Matrix n n 𝕜) (B : Matrix n q 𝕜) (C : Matrix p n 𝕜)
    (s t : ℕ) : (blockHankel A B C s t 0).rank ≤ Fintype.card n := by
  rw [blockHankel_zero_eq]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- Exact full-state ERA preserves every Markov parameter, not only the
finite parameters used to construct its Hankel matrix.
atlas: hankel-svd-era-realization (partial) -/
theorem IsThinSVD.era_markovParameter {A : Matrix n n 𝕜} {B : Matrix n q 𝕜}
    {C : Matrix p n 𝕜} {s t : ℕ} (hs : 0 < s) (ht : 0 < t)
    {U : Matrix (Fin s × p) n 𝕜} {V : Matrix (Fin t × q) n 𝕜} {σ : n → ℝ}
    (h : IsThinSVD (blockHankel A B C s t 0) U V σ) (j : ℕ) :
    eraOutputMatrix U σ (firstBlockOutput s hs) *
      eraStateMatrix (blockHankel A B C s t 1) U V σ ^ j *
        eraInputMatrix V σ (firstBlockInput t ht) = C * A ^ j * B := by
  obtain ⟨hT, hA, hB, hC⟩ := h.era_similarity hs ht
  rw [hA, hB, hC]
  exact markovParameter_eq_of_similarity A B C hT j

/-- The dimension recovered by a full-state Hankel SVD is minimal among
all realizations matching those finite Markov data. This is the rank
obstruction, and requires no stability assumption on either realization.
atlas: hankel-svd-era-realization (partial) -/
theorem IsThinSVD.card_le_of_markovParameters_eq {A : Matrix n n 𝕜}
    {B : Matrix n q 𝕜} {C : Matrix p n 𝕜} {s t : ℕ}
    {U : Matrix (Fin s × p) n 𝕜} {V : Matrix (Fin t × q) n 𝕜} {σ : n → ℝ}
    (h : IsThinSVD (blockHankel A B C s t 0) U V σ)
    {k : Type*} [Fintype k] [DecidableEq k]
    (A' : Matrix k k 𝕜) (B' : Matrix k q 𝕜) (C' : Matrix p k 𝕜)
    (hdata : ∀ j, j < s + t - 1 → C * A ^ j * B = C' * A' ^ j * B') :
    Fintype.card n ≤ Fintype.card k := by
  have hH : blockHankel A B C s t 0 = blockHankel A' B' C' s t 0 := by
    ext i j
    exact congr_fun (congr_fun (hdata (i.1.val + j.1.val)
      (by have hi := i.1.isLt; have hj := j.1.isLt; omega)) i.2) j.2
  calc
    Fintype.card n = (blockHankel A B C s t 0).rank := h.rank_eq_card.symm
    _ = (blockHankel A' B' C' s t 0).rank := congrArg Matrix.rank hH
    _ ≤ Fintype.card k := rank_blockHankel_le A' B' C' s t

end NLAlib
