import NLAlib.ForMathlib.MeasureTheory.Matrix
import NLAlib.Solvers.SketchAndProject.Core
import NLAlib.ForMathlib.Probability.PMF
import Mathlib.Probability.HasLaw

/-!
# Probability laws for sketch-and-project

`iidPathLaw` samples independent sketch indices from a native `PMF` and `run` executes
that path. `meanProjector` is the projector expectation. The primary
`integral_sqErr_iidPathLaw_le_of_sub_mem_range` theorem states row-space convergence
as an integral, and its `HasLaw` corollary applies on arbitrary sample spaces.
Finite weighted recurrences remain computational identities.
Source: Gower–Richtárik (2015), Theorem 4.6.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib.SketchProject
variable {m n s J : Type*} [Fintype m] [Fintype n] [Fintype s] [Fintype J]

/-- Apply the sketches in a finite chronological path.
Source: Gower–Richtárik (2015), equation (2.3). -/
def run (A : Matrix m n ℝ) (b : m → ℝ) (S : J → Matrix m s ℝ) :
    (k : ℕ) → (Fin k → J) → (n → ℝ) → (n → ℝ)
  | 0, _, x => x
  | k + 1, ω, x => run A b S k (Fin.tail ω) (step A b (S (ω 0)) x)

/-- The error recurrence computes the finite path-weighted squared errors. -/
theorem expErr_eq_sum_paths (A : Matrix m n ℝ) (b : m → ℝ)
    (p : J → ℝ) (S : J → Matrix m s ℝ) (xs x : n → ℝ) (k : ℕ) :
    expErr A b p S xs x k = ∑ ω : Fin k → J,
      (∏ j, p (ω j)) * ((run A b S k ω x - xs) ⬝ᵥ (run A b S k ω x - xs)) := by
  classical
  induction k generalizing x with
  | zero => simp [expErr, run]
  | succ k ih =>
    rw [expErr, ← (Fin.consEquiv fun _ => J).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp [Fin.consEquiv, run, Fin.prod_univ_succ, mul_assoc]

/-- Independent sketch indices have the product probability mass function.
Source: Gower–Richtárik (2015), finite iid sketch distribution. -/
def pathPMF (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (k : ℕ) : PMF (Fin k → J) := by
  classical
  refine PMF.ofFintype (fun ω => ENNReal.ofReal (∏ j, p (ω j))) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun ω _ => Finset.prod_nonneg fun j _ => hp (ω j))]
  have hsum : (∑ ω : Fin k → J, ∏ j, p (ω j)) = 1 := by
    rw [← Fintype.prod_sum]
    simp [hp1]
  simp [hsum]

/-- The measure of iid sketch paths. -/
def pathLaw [MeasurableSpace J] [MeasurableSingletonClass J]
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (k : ℕ) : Measure (Fin k → J) := (pathPMF p hp hp1 k).toMeasure

/-- The iid sketch path law is a probability measure. -/
instance pathLaw_isProbabilityMeasure [MeasurableSpace J] [MeasurableSingletonClass J]
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (k : ℕ) :
    IsProbabilityMeasure (pathLaw p hp hp1 k) := by
  unfold pathLaw
  infer_instance

/-- The integral of the random iterate's squared error is the error recurrence. -/
theorem integral_sqErr_pathLaw [MeasurableSpace J] [MeasurableSingletonClass J]
    (A : Matrix m n ℝ) (b : m → ℝ) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (S : J → Matrix m s ℝ) (xs x : n → ℝ) (k : ℕ) :
    (∫ ω, ‖WithLp.toLp 2 (run A b S k ω x - xs)‖ ^ 2
      ∂pathLaw p hp hp1 k) = expErr A b p S xs x k := by
  classical
  simp_rw [norm_toLp_sq_eq_dotProduct_self]
  rw [pathLaw, PMF.integral_eq_sum, expErr_eq_sum_paths]
  apply Finset.sum_congr rfl
  intro ω _
  change (ENNReal.ofReal (∏ j, p (ω j))).toReal • _ = _
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun j _ => hp (ω j))]
  rfl

/-- Sketch-and-project contracts the random iterate's expected squared error.
Source: Gower–Richtárik (2015), Theorem 4.6, Euclidean case and finite sketches.
atlas: sketch-and-project (partial) -/
theorem integral_sqErr_pathLaw_le [MeasurableSpace J] [MeasurableSingletonClass J]
    (A : Matrix m n ℝ) (b : m → ℝ) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (S : J → Matrix m s ℝ) {xs : n → ℝ} (hxs : A *ᵥ xs = b) {lam : ℝ}
    (hlam : ∀ v : n → ℝ, lam * ‖WithLp.toLp 2 v‖ ^ 2 ≤ v ⬝ᵥ (expectedProjector A p S *ᵥ v))
    (x : n → ℝ) (k : ℕ) :
    (∫ ω, ‖WithLp.toLp 2 (run A b S k ω x - xs)‖ ^ 2
      ∂pathLaw p hp hp1 k) ≤ (1 - lam) ^ k * ‖WithLp.toLp 2 (x - xs)‖ ^ 2 := by
  rw [integral_sqErr_pathLaw]
  simpa only [norm_toLp_sq_eq_dotProduct_self] using
    expErr_le A b p hp hp1 S hxs
      (by simpa only [norm_toLp_sq_eq_dotProduct_self] using hlam) x k

/-- Sketch-and-project contracts expected squared error for an initial row-space error.
Source: Gower–Richtárik (2015), Theorem 4.6, Euclidean case and finite sketches.
atlas: sketch-and-project (partial) -/
theorem integral_sqErr_pathLaw_le_of_sub_mem_range
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (A : Matrix m n ℝ) (b : m → ℝ) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (S : J → Matrix m s ℝ) {xs : n → ℝ} (hxs : A *ᵥ xs = b) {lam : ℝ}
    (hlam : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      lam * ‖WithLp.toLp 2 v‖ ^ 2 ≤ v ⬝ᵥ (expectedProjector A p S *ᵥ v))
    (x : n → ℝ) (hx : x - xs ∈ LinearMap.range Aᵀ.mulVecLin) (k : ℕ) :
    (∫ ω, ‖WithLp.toLp 2 (run A b S k ω x - xs)‖ ^ 2
      ∂pathLaw p hp hp1 k) ≤ (1 - lam) ^ k * ‖WithLp.toLp 2 (x - xs)‖ ^ 2 := by
  rw [integral_sqErr_pathLaw]
  simpa only [norm_toLp_sq_eq_dotProduct_self] using
    expErr_le_of_sub_mem_range A b p hp hp1 S hxs
      (by simpa only [norm_toLp_sq_eq_dotProduct_self] using hlam) x hx k

/-- A sketch path with the iid law has the same squared-error integral. -/
theorem integral_sqErr_pathLaw_of_hasLaw
    [MeasurableSpace J] [MeasurableSingletonClass J]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Matrix m n ℝ) (b : m → ℝ) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (S : J → Matrix m s ℝ) (xs x : n → ℝ) (k : ℕ)
    {H : Ω → Fin k → J} (hH : HasLaw H (pathLaw p hp hp1 k) μ) :
    (∫ ω, ‖WithLp.toLp 2 (run A b S k (H ω) x - xs)‖ ^ 2 ∂μ) =
      expErr A b p S xs x k := by
  rw [← integral_sqErr_pathLaw A b p hp hp1 S xs x k]
  exact hH.integral_comp ((measurable_of_finite (fun h : Fin k → J =>
    ‖WithLp.toLp 2 (run A b S k h x - xs)‖ ^ 2)).aestronglyMeasurable)

/-- Row-space convergence transports to a sketch path on an arbitrary probability space.
Source: Gower–Richtárik (2015), Theorem 4.6. -/
theorem integral_sqErr_pathLaw_le_of_sub_mem_range_of_hasLaw
    [MeasurableSpace J] [MeasurableSingletonClass J]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Matrix m n ℝ) (b : m → ℝ) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (S : J → Matrix m s ℝ) {xs : n → ℝ} (hxs : A *ᵥ xs = b) {lam : ℝ}
    (hlam : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      lam * ‖WithLp.toLp 2 v‖ ^ 2 ≤ v ⬝ᵥ (expectedProjector A p S *ᵥ v))
    (x : n → ℝ) (hx : x - xs ∈ LinearMap.range Aᵀ.mulVecLin) (k : ℕ)
    {H : Ω → Fin k → J} (hH : HasLaw H (pathLaw p hp hp1 k) μ) :
    (∫ ω, ‖WithLp.toLp 2 (run A b S k (H ω) x - xs)‖ ^ 2 ∂μ) ≤
      (1 - lam) ^ k * ‖WithLp.toLp 2 (x - xs)‖ ^ 2 := by
  rw [integral_sqErr_pathLaw_of_hasLaw A b p hp hp1 S xs x k hH]
  simpa only [norm_toLp_sq_eq_dotProduct_self] using
    expErr_le_of_sub_mem_range A b p hp hp1 S hxs
      (by simpa only [norm_toLp_sq_eq_dotProduct_self] using hlam) x hx k

/-- The probability mass function of one sketch index. -/
def sketchPMF (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) : PMF J := by
  classical
  refine PMF.ofFintype (fun j => ENNReal.ofReal (p j)) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hp j), hp1]
  simp

/-- The probability measure of one sketch index. -/
def sketchLaw [MeasurableSpace J] [MeasurableSingletonClass J]
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) : Measure J :=
  (sketchPMF p hp hp1).toMeasure

/-- The sketch-index law is a probability measure. -/
instance sketchLaw_isProbabilityMeasure [MeasurableSpace J] [MeasurableSingletonClass J]
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) :
    IsProbabilityMeasure (sketchLaw p hp hp1) := by
  unfold sketchLaw
  infer_instance

open scoped Matrix.Norms.Frobenius in
/-- The finite projector formula is the expectation of the sampled row-space projector.
Source: Gower–Richtárik (2015), equation (4.1). -/
theorem integral_projector_sketchLaw [MeasurableSpace J] [MeasurableSingletonClass J]
    (A : Matrix m n ℝ) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (S : J → Matrix m s ℝ) :
    (∫ j, moorePenroseInverse ((S j)ᵀ * A) * ((S j)ᵀ * A)
      ∂sketchLaw p hp hp1) = expectedProjector A p S := by
  classical
  rw [sketchLaw, PMF.integral_eq_sum]
  unfold expectedProjector
  apply Finset.sum_congr rfl
  intro j _
  change (ENNReal.ofReal (p j)).toReal • _ = _
  rw [ENNReal.toReal_ofReal (hp j)]

open scoped Matrix.Norms.Frobenius in
/-- A sampled projector's expectation transports through its sketch-index law. -/
theorem integral_projector_sketchLaw_of_hasLaw
    [MeasurableSpace J] [MeasurableSingletonClass J]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Matrix m n ℝ) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (S : J → Matrix m s ℝ)
    {I : Ω → J} (hI : HasLaw I (sketchLaw p hp hp1) μ) :
    (∫ ω, moorePenroseInverse ((S (I ω))ᵀ * A) * ((S (I ω))ᵀ * A) ∂μ) =
      expectedProjector A p S := by
  rw [← integral_projector_sketchLaw A p hp hp1 S]
  exact hI.integral_comp ((StronglyMeasurable.of_discrete (f := fun j : J =>
    moorePenroseInverse ((S j)ᵀ * A) * ((S j)ᵀ * A))).aestronglyMeasurable)


/-- Independent sketch paths drawn from a probability mass function.
Source: Gower–Richtárik (2015), iid sketches. -/
def iidPathPMF (q : PMF J) (k : ℕ) : PMF (Fin k → J) := by
  classical
  refine PMF.ofFintype (fun ω => ∏ j, q (ω j)) ?_
  rw [← Fintype.prod_sum]
  have hsum : ∑ j, q j = 1 := by simpa only [tsum_fintype] using q.tsum_coe
  simp [hsum]

/-- The law of independent sketch paths from a native PMF. -/
def iidPathLaw [MeasurableSpace J] [MeasurableSingletonClass J]
    (q : PMF J) (k : ℕ) : Measure (Fin k → J) := (iidPathPMF q k).toMeasure

/-- Independent sketch paths have a probability law. -/
instance iidPathLaw_isProbabilityMeasure [MeasurableSpace J] [MeasurableSingletonClass J]
    (q : PMF J) (k : ℕ) : IsProbabilityMeasure (iidPathLaw q k) := by
  unfold iidPathLaw
  infer_instance

open scoped Matrix.Norms.Frobenius in
/-- The mean sketch projector under a native sketch distribution.
Source: Gower–Richtárik (2015), equation (4.1). -/
def meanProjector [MeasurableSpace J] [MeasurableSingletonClass J]
    (A : Matrix m n ℝ) (q : PMF J) (S : J → Matrix m s ℝ) : Matrix n n ℝ :=
  ∫ j, moorePenroseInverse ((S j)ᵀ * A) * ((S j)ᵀ * A) ∂q.toMeasure

open scoped Matrix.Norms.Frobenius in
/-- The mean projector is computed by the finite real-mass projector sum. -/
theorem meanProjector_eq_expectedProjector [MeasurableSpace J] [MeasurableSingletonClass J]
    (A : Matrix m n ℝ) (q : PMF J) (S : J → Matrix m s ℝ) :
    meanProjector A q S = expectedProjector A (fun j => (q j).toReal) S := by
  rw [meanProjector, PMF.integral_eq_sum]
  rfl

/-- The random-run squared-error integral is computed by the finite recurrence. -/
theorem integral_sqErr_iidPathLaw [MeasurableSpace J] [MeasurableSingletonClass J]
    (A : Matrix m n ℝ) (b : m → ℝ) (q : PMF J)
    (S : J → Matrix m s ℝ) (xs x : n → ℝ) (k : ℕ) :
    (∫ ω, ‖WithLp.toLp 2 (run A b S k ω x - xs)‖ ^ 2 ∂iidPathLaw q k) =
      expErr A b (fun j => (q j).toReal) S xs x k := by
  classical
  simp_rw [norm_toLp_sq_eq_dotProduct_self]
  rw [iidPathLaw, PMF.integral_eq_sum, expErr_eq_sum_paths]
  apply Finset.sum_congr rfl
  intro ω _
  change (∏ j, q (ω j)).toReal • _ = _
  rw [ENNReal.toReal_prod]
  rfl

/-- A random history with the iid law has the same squared-error integral. -/
theorem integral_sqErr_iidPathLaw_of_hasLaw
    [MeasurableSpace J] [MeasurableSingletonClass J]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Matrix m n ℝ) (b : m → ℝ) (q : PMF J)
    (S : J → Matrix m s ℝ) (xs x : n → ℝ) (k : ℕ)
    {H : Ω → Fin k → J} (hH : HasLaw H (iidPathLaw q k) μ) :
    (∫ ω, ‖WithLp.toLp 2 (run A b S k (H ω) x - xs)‖ ^ 2 ∂μ) =
      expErr A b (fun j => (q j).toReal) S xs x k := by
  rw [← integral_sqErr_iidPathLaw A b q S xs x k]
  exact hH.integral_comp ((measurable_of_finite (fun h : Fin k → J =>
    ‖WithLp.toLp 2 (run A b S k h x - xs)‖ ^ 2)).aestronglyMeasurable)

/-- Sketch-and-project contracts expected squared error for an initial row-space error
under a native sketch probability mass function.
Source: Gower–Richtárik (2015), Theorem 4.6, Euclidean case and finite sketches.
atlas: sketch-and-project -/
theorem integral_sqErr_iidPathLaw_le_of_sub_mem_range
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (A : Matrix m n ℝ) (b : m → ℝ) (q : PMF J) (S : J → Matrix m s ℝ)
    {xs : n → ℝ} (hxs : A *ᵥ xs = b) {lam : ℝ}
    (hlam : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      lam * ‖WithLp.toLp 2 v‖ ^ 2 ≤ v ⬝ᵥ (meanProjector A q S *ᵥ v))
    (x : n → ℝ) (hx : x - xs ∈ LinearMap.range Aᵀ.mulVecLin) (k : ℕ) :
    (∫ ω, ‖WithLp.toLp 2 (run A b S k ω x - xs)‖ ^ 2 ∂iidPathLaw q k) ≤
      (1 - lam) ^ k * ‖WithLp.toLp 2 (x - xs)‖ ^ 2 := by
  rw [integral_sqErr_iidPathLaw]
  simpa only [norm_toLp_sq_eq_dotProduct_self] using
    expErr_le_of_sub_mem_range A b (fun j => (q j).toReal)
      (fun _ => ENNReal.toReal_nonneg) q.sum_toReal S hxs
      (by simpa only [norm_toLp_sq_eq_dotProduct_self, meanProjector_eq_expectedProjector] using hlam)
      x hx k

/-- Native sketch-and-project convergence transports to an arbitrary sample space.
Source: Gower–Richtárik (2015), Theorem 4.6. -/
theorem integral_sqErr_iidPathLaw_le_of_sub_mem_range_of_hasLaw
    [MeasurableSpace J] [MeasurableSingletonClass J]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Matrix m n ℝ) (b : m → ℝ) (q : PMF J) (S : J → Matrix m s ℝ)
    {xs : n → ℝ} (hxs : A *ᵥ xs = b) {lam : ℝ}
    (hlam : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      lam * ‖WithLp.toLp 2 v‖ ^ 2 ≤ v ⬝ᵥ (meanProjector A q S *ᵥ v))
    (x : n → ℝ) (hx : x - xs ∈ LinearMap.range Aᵀ.mulVecLin) (k : ℕ)
    {H : Ω → Fin k → J} (hH : HasLaw H (iidPathLaw q k) μ) :
    (∫ ω, ‖WithLp.toLp 2 (run A b S k (H ω) x - xs)‖ ^ 2 ∂μ) ≤
      (1 - lam) ^ k * ‖WithLp.toLp 2 (x - xs)‖ ^ 2 := by
  rw [integral_sqErr_iidPathLaw_of_hasLaw A b q S xs x k hH,
    ← integral_sqErr_iidPathLaw A b q S xs x k]
  exact integral_sqErr_iidPathLaw_le_of_sub_mem_range A b q S hxs hlam x hx k

/-- An independent path has the product of its sketch-index masses. -/
theorem iidPathLaw_singleton [MeasurableSpace J] [MeasurableSingletonClass J]
    (q : PMF J) (k : ℕ) (h : Fin k → J) :
    (iidPathLaw q k).real {h} = ∏ j, (q (h j)).toReal := by
  classical
  rw [Measure.real, iidPathLaw,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change (∏ j, q (h j)).toReal = _
  exact ENNReal.toReal_prod _ _

open scoped Matrix.Norms.Frobenius in
/-- The distribution of the sampled projector transports through a sketch-index law. -/
theorem integral_projector_eq_meanProjector_of_hasLaw
    [MeasurableSpace J] [MeasurableSingletonClass J]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Matrix m n ℝ) (q : PMF J) (S : J → Matrix m s ℝ)
    {I : Ω → J} (hI : HasLaw I q.toMeasure μ) :
    (∫ ω, moorePenroseInverse ((S (I ω))ᵀ * A) * ((S (I ω))ᵀ * A) ∂μ) =
      meanProjector A q S := by
  exact hI.integral_comp ((StronglyMeasurable.of_discrete (f := fun j : J =>
    moorePenroseInverse ((S j)ᵀ * A) * ((S j)ᵀ * A))).aestronglyMeasurable)

/-- A lower quadratic bound for the mean projector on the whole space gives convergence
for every initial iterate under a native sketch probability mass function.
Source: Gower–Richtárik (2015), Theorem 4.6, Euclidean case and finite sketches.
atlas: sketch-and-project (partial) -/
theorem integral_sqErr_iidPathLaw_le
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (A : Matrix m n ℝ) (b : m → ℝ) (q : PMF J) (S : J → Matrix m s ℝ)
    {xs : n → ℝ} (hxs : A *ᵥ xs = b) {lam : ℝ}
    (hlam : ∀ v : n → ℝ,
      lam * ‖WithLp.toLp 2 v‖ ^ 2 ≤ v ⬝ᵥ (meanProjector A q S *ᵥ v))
    (x : n → ℝ) (k : ℕ) :
    (∫ ω, ‖WithLp.toLp 2 (run A b S k ω x - xs)‖ ^ 2 ∂iidPathLaw q k) ≤
      (1 - lam) ^ k * ‖WithLp.toLp 2 (x - xs)‖ ^ 2 := by
  rw [integral_sqErr_iidPathLaw]
  simpa only [norm_toLp_sq_eq_dotProduct_self] using
    expErr_le A b (fun j => (q j).toReal)
      (fun _ => ENNReal.toReal_nonneg) q.sum_toReal S hxs
      (by simpa only [norm_toLp_sq_eq_dotProduct_self, meanProjector_eq_expectedProjector] using hlam)
      x k

end NLAlib.SketchProject
