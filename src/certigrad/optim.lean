/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Algorithms for optimization.
-/
import .tensor .tvec .dvec

namespace certigrad
namespace optim

namespace adam
structure params : Type := (α β₁ β₂ ε : ℝ)

structure state (shapes : list S) : Type := (m₀ v₀ : dvec T shapes) (t : ℕ)

def init_state {shapes : list S} : state shapes := ⟨0, 0, 0⟩
def default_params : params := ⟨1/1000, 9/10, 999/1000, T.pow 10 (- 8)⟩

def step_core_slow {shapes : list S} (θ grads : dvec T shapes) : Π (ps : params)  (st : state shapes), dvec T shapes × state shapes
| (params.mk α β₁ β₂ ε : params) (state.mk m_old v_old t_old : state shapes) :=
  let t := t_old + 1,
      m := β₁ ⬝ m_old + (1 - β₁) ⬝ grads,
      v := β₂ ⬝ v_old + (1 - β₂) ⬝ (grads * grads),
      m' := m / ((1 - T.pow β₁ (T.of_nat t)) ⬝ 1),
      v' := v / ((1 - T.pow β₂ (T.of_nat t)) ⬝ 1)
  in
    (θ - α ⬝ (m' / (tvec.sqrt v' + ε ⬝ 1)), state.mk m v t)

def step_core {shapes : list S} (θ grads : dvec T shapes) : Π (ps : params)  (st : state shapes), dvec T shapes × state shapes
| (params.mk α β₁ β₂ ε : params) (state.mk m_old v_old t_old : state shapes) :=
  let t := t_old + 1,
      m := β₁ ⬝ m_old + (1 - β₁) ⬝ grads,
      v := β₂ ⬝ v_old + (1 - β₂) ⬝ (grads * grads),
      γ := α * T.sqrt (1 - T.pow β₂ (T.of_nat t)) / (1 - T.pow β₁ (T.of_nat t))
  in
    (θ - γ ⬝ (m / (tvec.sqrt v + ε ⬝ 1)), state.mk m v t)

-- Exercise for the reader: state and prove that `step_core` is correct, i.e. that it computes the same function as `step_core_slow`.

def step {shapes : list S} (θ grads : dvec T shapes) : Π (st : state shapes), dvec T shapes × state shapes :=
  step_core θ grads default_params

end adam
end optim
end certigrad
