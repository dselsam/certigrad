import .util .naive ..prove_model_ok ..pre

set_option class.instance_max_depth 1000000
set_option max_memory 10000000
set_option pp.max_depth 100000

namespace certigrad
namespace T

-- ω(exp -x²) ∧ o(exp x²)
constant is_btw_exp₂ {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : Prop
constant is_linear {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : Prop

axiom is_integrable_mvn_of_sub_exp {shape₁ shape₂ : S} (μ σ : T shape₁) (f : T shape₁ → T shape₂) :
  is_btw_exp₂ f → T.is_integrable (λ x, T.mvn_iso_pdf μ σ x ⬝ f x)

-- btw axioms

axiom is_btw_id {shape : S} : is_btw_exp₂ (λ (x : T shape), x)
axiom is_btw_const {shape₁ shape₂ : S} (y : T shape₂) : is_btw_exp₂ (λ (x : T shape₁), y)
axiom is_btw_sigmoid {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : is_btw_exp₂ (λ (x : T shape₁), sigmoid (f x))
axiom is_btw_softplus {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ (λ (x : T shape₁), softplus (f x))

axiom is_btw_gemm {shape : S} {m n p : ℕ} (f : T shape → T [m, n]) (g : T shape → T [n, p]) :
  is_btw_exp₂ f → is_btw_exp₂ g → is_btw_exp₂ (λ x, gemm (f x) (g x))

axiom is_btw_neg {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ (λ x, - (f x))
axiom is_btw_inv {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ (λ x, (f x)⁻¹)
axiom is_btw_add {shape₁ shape₂ : S} (f g : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ g → is_btw_exp₂ (λ x, f x + g x)
axiom is_btw_mul {shape₁ shape₂ : S} (f g : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ g → is_btw_exp₂ (λ x, f x * g x)
axiom is_btw_sub {shape₁ shape₂ : S} (f g : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ g → is_btw_exp₂ (λ x, f x - g x)
axiom is_btw_div {shape₁ shape₂ : S} (f g : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ g → is_btw_exp₂ (λ x, f x / g x)

axiom is_btw_exp {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : is_linear f → is_btw_exp₂ (λ x, exp (f x))

-- linear axioms


end T

section tactic
open tactic

meta def prove_is_mvn_integrable_core : tactic unit :=
first [
       applyc `certigrad.T.is_btw_id
     , applyc `certigrad.T.is_btw_const
     , applyc `certigrad.T.is_btw_sigmoid
     , applyc `certigrad.T.is_btw_softplus
     , applyc `certigrad.T.is_btw_gemm
     , applyc `certigrad.T.is_btw_neg
     , applyc `certigrad.T.is_btw_inv
     , applyc `certigrad.T.is_btw_add
     , applyc `certigrad.T.is_btw_mul
     , applyc `certigrad.T.is_btw_sub
     , applyc `certigrad.T.is_btw_div
]

meta def prove_is_mvn_integrable : tactic unit :=
do applyc `certigrad.T.is_integrable_mvn_of_sub_exp,
   repeat_at_most 100 prove_is_mvn_integrable_core

end tactic

end certigrad
