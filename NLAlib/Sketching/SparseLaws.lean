import NLAlib.Sketching.SparseFock.UniformExactSModel
import NLAlib.ForMathlib.Probability.FiniteLawMeasure

/-!
# Actual measures for SparseStack and uniform signed sparse columns

The explicit independent finite laws from the pinned sparse-Fock proof are
actual Mathlib probability measures. Each selector has a uniform row and
independent sign; each exact-s column has a uniform support and independent
signs. Source: manuscript `sh:sparse`, pinned sparse-Fock commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`. Atlas: `sparse-ose`.
-/

noncomputable section
set_option autoImplicit false
namespace NLAlib

/-- The two signs carry the discrete sigma-algebra. Source: the explicit
SparseStack sampling construction; supports `sparse-ose`. -/
instance SparseFock.SparseStackModel.Sign.instMeasurableSpace :
    MeasurableSpace SparseFock.SparseStackModel.Sign := ⊤

/-- Every sign singleton is measurable. Source: discrete finite sampling;
supports `sparse-ose`. -/
instance SparseFock.SparseStackModel.Sign.instMeasurableSingletonClass :
    MeasurableSingletonClass SparseFock.SparseStackModel.Sign := ⟨fun _ => trivial⟩

/-- Exact-size supports carry the discrete sigma-algebra. Source: the explicit
uniform support construction; supports `sparse-ose`. -/
instance SparseFock.UniformExactS.instMeasurableSpaceExactSupport (m s : ℕ) :
    MeasurableSpace (SparseFock.UniformExactS.ExactSupport m s) := ⊤

/-- Every exact-size support singleton is measurable. Source: discrete finite
sampling; supports `sparse-ose`. -/
instance SparseFock.UniformExactS.instMeasurableSingletonClassExactSupport (m s : ℕ) :
    MeasurableSingletonClass (SparseFock.UniformExactS.ExactSupport m s) :=
  ⟨fun _ => trivial⟩

/-- The actual independent uniform signed-selector measure for an s-block
SparseStack. Source: pinned sparse-Fock product weights; supports `sparse-ose`. -/
def sparseStackMeasure (s b n : ℕ) (hb : 0 < b) :
    MeasureTheory.Measure (SparseFock.SparseStackDistribution.RawSample s b n) :=
  (SparseFock.SparseStackDistribution.rawSampleLaw s b n hb).toMeasure

/-- SparseStack's actual law is a probability measure. Source: normalized
product weights; supports `sparse-ose`. -/
instance sparseStackMeasure_isProbabilityMeasure (s b n : ℕ) (hb : 0 < b) :
    MeasureTheory.IsProbabilityMeasure (sparseStackMeasure s b n hb) := by
  unfold sparseStackMeasure
  infer_instance

/-- The actual independent-column law for uniformly chosen signed supports
of size exactly s. Source: pinned exact-s construction; supports `sparse-ose`. -/
def uniformSparseMeasure (m s n : ℕ) (hsm : s ≤ m) :
    MeasureTheory.Measure (SparseFock.UniformExactS.ExactSample m s n) :=
  (SparseFock.UniformExactS.exactSampleLaw hsm).toMeasure

/-- The uniform signed sparse law is a probability measure. Source: normalized
independent uniform-column weights; supports `sparse-ose`. -/
instance uniformSparseMeasure_isProbabilityMeasure (m s n : ℕ) (hsm : s ≤ m) :
    MeasureTheory.IsProbabilityMeasure (uniformSparseMeasure m s n hsm) := by
  unfold uniformSparseMeasure
  infer_instance

end NLAlib
