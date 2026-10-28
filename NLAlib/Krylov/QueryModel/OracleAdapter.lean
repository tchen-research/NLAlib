import NLAlib.Krylov.QueryModel.Program

/-! # Response adapters preserve the number of primitive oracle queries -/

namespace NLAlib.QueryProgram
variable {Q R S β : Type*} {q : ℕ}

/-- Interpret each primitive response through a fixed function, with no extra
oracle call. In particular, known matrix scales can be removed this way. -/
def adaptResponses (g : S → R) : {q : ℕ} → QueryProgram Q R β q → QueryProgram Q S β q
  | _, .pure value => .pure value
  | _, .query value next => .query value (fun response => adaptResponses g (next (g response)))

/-- Running an adapted strategy is exactly running its original strategy with
the correspondingly adapted oracle. -/
@[simp] theorem run_adaptResponses (g : S → R) (f : Q → S) (p : QueryProgram Q R β q) :
    (adaptResponses g p).run f = p.run (g ∘ f) := by
  induction p with
  | pure value => rfl
  | query value next ih => exact ih (g (f value))

end NLAlib.QueryProgram
