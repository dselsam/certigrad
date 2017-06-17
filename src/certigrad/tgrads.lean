/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Properties of gradients.
-/
import .tensor .tfacts .tactics

namespace certigrad
namespace T
open list

-- is_cdifferentiable

axiom is_cdifferentiable_binary {shape : S} (k : T shape → T shape → ℝ) (θ : T shape) :
  is_cdifferentiable (λ θ₀, k θ₀ θ) θ → is_cdifferentiable (λ θ₀, k θ θ₀) θ →
  is_cdifferentiable (λ θ₀, k θ₀ θ₀) θ

axiom is_cdifferentiable_multiple_args {fshape : S} (tgt : reference) (parents : list reference) (m : env) (f : dvec T parents^.p2 → T fshape)
                                      (θ : T tgt.2) (k : T fshape → ℝ) :
  (∀ (idx : ℕ) (H_idx_in_riota: idx ∈ riota (length parents)) (H_tgt_eq_dnth_idx : tgt = dnth parents idx),
     is_cdifferentiable (λ θ₀, k (f (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ m)) idx))) θ) →
  is_cdifferentiable (λ θ₀, k (f (env.get_ks parents (env.insert tgt θ₀ m)))) θ

axiom is_cdifferentiable_integral : ∀ {ishape tshape : S} (f : T ishape → T tshape → ℝ) (θ : T tshape),
  (∀ x, is_cdifferentiable (f x) θ) →
  is_uniformly_integrable_around (λ θ₀ x, f x θ₀) θ →
  is_uniformly_integrable_around (λ θ₀ x, ∇ (λ θ₁, f x θ₁) θ₀) θ →
  is_cdifferentiable (λ θ₀, ∫ (λ x, f x θ₀)) θ

axiom is_cdifferentiable_const {ishape : S} (θ : T ishape) (x : ℝ) : is_cdifferentiable (λ (θ₀ : T ishape), x) θ
axiom is_cdifferentiable_id (θ : ℝ) : is_cdifferentiable (λ (θ₀ : ℝ), θ₀) θ

axiom is_cdifferentiable_exp {shape : S} (k : T shape → ℝ) (θ : T shape) :
  is_cdifferentiable k (exp θ) → is_cdifferentiable (λ θ, k (exp θ)) θ

axiom is_cdifferentiable_log {shape : S} (k : T shape → ℝ) (θ : T shape) : θ > 0 →
  is_cdifferentiable k (log θ) → is_cdifferentiable (λ θ, k (log θ)) θ

axiom is_cdifferentiable_sqrt {shape : S} (k : T shape → ℝ) (θ : T shape) :
  is_cdifferentiable k (sqrt θ) → is_cdifferentiable (λ θ, k (sqrt θ)) θ

axiom is_cdifferentiable_inv {shape : S} (k : T shape → ℝ) (θ : T shape) : θ > 0 →
  is_cdifferentiable k θ⁻¹ → is_cdifferentiable (λ θ, k θ⁻¹) θ

axiom is_cdifferentiable_scale {shape : S} (k : T shape → ℝ) (α : ℝ) (x : T shape) :
  is_cdifferentiable k (α ⬝ x) → is_cdifferentiable (λ x, k (α ⬝ x)) x

axiom is_cdifferentiable_neg {shape : S} (k : T shape → ℝ) (θ : T shape) :
  is_cdifferentiable k (- θ) → is_cdifferentiable (λ θ, k (- θ)) θ

axiom is_cdifferentiable_add₁ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ + x₂) → is_cdifferentiable (λ x₁, k (x₁ + x₂)) x₁

axiom is_cdifferentiable_add₂ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ + x₂) → is_cdifferentiable (λ x₂, k (x₁ + x₂)) x₂

axiom is_cdifferentiable_sub₁ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ - x₂) → is_cdifferentiable (λ x₁, k (x₁ - x₂)) x₁

axiom is_cdifferentiable_sub₂ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ - x₂) → is_cdifferentiable (λ x₂, k (x₁ - x₂)) x₂

axiom is_cdifferentiable_mul₁ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ * x₂) → is_cdifferentiable (λ x₁, k (x₁ * x₂)) x₁

axiom is_cdifferentiable_mul₂ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ * x₂) → is_cdifferentiable (λ x₂, k (x₁ * x₂)) x₂

axiom is_cdifferentiable_div₁ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) : square x₂ > 0 →
  is_cdifferentiable k (x₁ / x₂) → is_cdifferentiable (λ x₁, k (x₁ / x₂)) x₁

axiom is_cdifferentiable_div₂ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) : square x₂ > 0 →
  is_cdifferentiable k (x₁ / x₂) → is_cdifferentiable (λ x₂, k (x₁ / x₂)) x₂

axiom is_cdifferentiable_sum (k : ℝ → ℝ) (shape : S) (x : T shape) :
  is_cdifferentiable k (sum x) → is_cdifferentiable (λ x, k (sum x)) x

axiom is_cdifferentiable_prod (k : ℝ → ℝ) (shape : S) (x : T shape) :
  is_cdifferentiable k (prod x) → is_cdifferentiable (λ x, k (prod x)) x

axiom is_cdifferentiable_square {shape : S} (k : T shape → ℝ) (x : T shape) :
  is_cdifferentiable k (square x) → is_cdifferentiable (λ x, k (square x)) x

axiom is_cdifferentiable_gemm₁ {m p : ℕ} (k : T [m, p] → ℝ) (n : ℕ) (M : T [m, n]) (N : T [n, p]) :
  is_cdifferentiable k (gemm M N) → is_cdifferentiable (λ M, k (gemm M N)) M

axiom is_cdifferentiable_gemm₂ {m p : ℕ} (k : T [m, p] → ℝ) (n : ℕ) (M : T [m, n]) (N : T [n, p]) :
  is_cdifferentiable k (gemm M N) → is_cdifferentiable (λ N, k (gemm M N)) N

axiom is_cdifferentiable_add_fs {shape : S} (f₁ f₂ : T shape → ℝ) (θ : T shape):
  (is_cdifferentiable f₁ θ ∧ is_cdifferentiable f₂ θ) ↔ is_cdifferentiable (λ θ₀, f₁ θ₀ + f₂ θ₀) θ

axiom is_cdifferentiable_scale_f {shape : S} (α : ℝ) (f : T shape → ℝ) (θ : T shape):
  is_cdifferentiable f θ ↔ is_cdifferentiable (λ x, α ⬝ f x) θ

axiom is_cdifferentiable_fscale {shape : S} (f : T shape → ℝ) (y : ℝ) (θ : T shape):
  is_cdifferentiable f θ ↔ is_cdifferentiable (λ x, f x ⬝ y) θ

-- Provable
axiom is_cdifferentiable_sumr {X : Type} {shape : S} (θ : T shape) (f : T shape → X → ℝ) :
  Π (xs : list X),
    (∀ (x : X), x ∈ xs → is_cdifferentiable (λ θ₀, f θ₀ x) θ) →
    is_cdifferentiable (λ (θ₀ : T shape), sumr (map (f θ₀) xs)) θ

--

axiom grad_binary {shape : S} (k : T shape → T shape → ℝ) (θ : T shape) :
  is_cdifferentiable (λ θ₀, k θ₀ θ) θ → is_cdifferentiable (λ θ₀, k θ θ₀) θ →
  ∇ (λ θ₀, k θ₀ θ₀) θ = ∇ (λ θ₀, k θ₀ θ) θ + ∇ (λ θ₀, k θ θ₀) θ

axiom grad_tmulT {ishape oshape : S} : ∀ (f : T ishape → T oshape) (k : T oshape → ℝ) (θ : T ishape),
  ∇ (λ θ₀, k (f θ₀)) θ = tmulT (D (λ θ₀, f θ₀) θ) (∇ k (f θ))

axiom grad_chain_rule : ∀ {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) (g : T shape₂ → ℝ) (θ : T shape₁),
  ∇ (λ (θ₀ : T shape₁), g (f θ₀)) θ = tmulT (D f θ) (∇ g (f θ))

-- See Lang (Page 340, Theorem 3.4)
-- f continuously differentiable
-- f and grad_2 f both uniformly integrable
axiom grad_integral : ∀ {ishape tshape : S} (f : T ishape → T tshape → ℝ) (θ : T tshape),
  (∀ x, is_cdifferentiable (f x) θ) →
  is_uniformly_integrable_around (λ θ₀ x, f x θ₀) θ →
  is_uniformly_integrable_around (λ θ₀ x, ∇ (λ θ₁, f x θ₁) θ₀) θ →
  ∇ (λ θ₀, ∫ (λ x, f x θ₀)) θ = ∫ (λ x, ∇ (λ θ₀, f x θ₀) θ)

lemma grad_congr {shape : S} {f g : T shape → ℝ} {x : T shape} (H : ∀ x, f x = g x) : ∇ f x = ∇ g x :=
begin change (∇ (λ x, f x) x = ∇ (λ x, g x) x), rw (funext H) end

axiom grad_const : ∀ {ishape : S} (θ : T ishape) (x : ℝ), ∇ (λ (θ₀ : T ishape), x) θ = 0
axiom grad_id : ∀ (θ : ℝ), ∇ (λ θ, θ) θ = 1

-- Unary
axiom grad_exp {shape : S} (k : T shape → ℝ) (θ : T shape) :
  ∇ (λ θ, k (exp θ)) θ = ∇ k (exp θ) * exp θ

axiom grad_log {shape : S} (k : T shape → ℝ) (θ : T shape) : θ > 0 →
  ∇ (λ θ, k (log θ)) θ = ∇ k (log θ) / θ

axiom grad_sqrt {shape : S} (k : T shape → ℝ) (θ : T shape) : θ > 0 →
  ∇ (λ θ, k (sqrt θ)) θ = ∇ k (sqrt θ) / (2 * sqrt θ)

axiom grad_scale {shape : S} (k : T shape → ℝ) (α : ℝ) (x : T shape) :
  ∇ (λ x, k (α ⬝ x)) x = α ⬝ ∇ k (α ⬝ x)

axiom grad_neg {shape : S} (k : T shape → ℝ) (θ : T shape) :
  ∇ (λ θ, k (- θ)) θ = - (∇ k (- θ))

-- Binary
axiom grad_add₁ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) :
  ∇ (λ x₁, k (x₁ + x₂)) x₁ = ∇ k (x₁ + x₂)

axiom grad_add₂ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) :
  ∇ (λ x₂, k (x₁ + x₂)) x₂ = ∇ k (x₁ + x₂)

axiom grad_sub₁ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) :
  ∇ (λ x₁, k (x₁ - x₂)) x₁ = ∇ k (x₁ - x₂)

axiom grad_sub₂ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) :
  ∇ (λ x₂, k (x₁ - x₂)) x₂ = - ∇ k (x₁ - x₂)

axiom grad_mul₁ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) :
  ∇ (λ x₁, k (x₁ * x₂)) x₁ = ∇ k (x₁ * x₂) * x₂

axiom grad_mul₂ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) :
  ∇ (λ x₂, k (x₁ * x₂)) x₂ = ∇ k (x₁ * x₂) * x₁

-- Note: can be proved from grad_binary and grad_mul*, but resulting theorem
-- would have `is_cdifferentiable k` as a pre-condition.
-- It is safe to avoid that here because of the symmetry of the function.
axiom grad_square {shape : S} (k : T shape → ℝ) (x : T shape) :
  ∇ (λ x, k (square x)) x = ∇ k (square x) * 2 * x

axiom grad_div₁ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) : square x₂ > 0 →
  ∇ (λ x₁, k (x₁ / x₂)) x₁ = ∇ k (x₁ / x₂) / x₂

axiom grad_div₂ {shape : S} (k : T shape → ℝ) (x₁ x₂ : T shape) : square x₂ > 0 →
  ∇ (λ x₂, k (x₁ / x₂)) x₂ = - (∇ k (x₁ / x₂) * x₁) / (square x₂)

-- Tensors
axiom grad_sum (k : ℝ → ℝ) (shape : S) (x : T shape) :
  ∇ (λ x, k (sum x)) x = ∇ k (sum x) ⬝ 1

axiom grad_dot₁ {shape : S} (x₁ x₂ : T shape) : ∇ (λ x₁, dot x₁ x₂) x₁ = x₂
axiom grad_dot₂ {shape : S} (x₁ x₂ : T shape) : ∇ (λ x₂, dot x₁ x₂) x₂ = x₁

axiom grad_gemm₁ {m p : ℕ} (k : T [m, p] → ℝ) (n : ℕ) (M : T [m, n]) (N : T [n, p]) :
∇ (λ M, k (gemm M N)) M = gemm (∇ k (gemm M N)) (transpose N)

axiom grad_gemm₂ {m p : ℕ} (k : T [m, p] → ℝ) (n : ℕ) (M : T [m, n]) (N : T [n, p]) :
∇ (λ N, k (gemm M N)) N = gemm (transpose M) (∇ k (gemm M N))

-- Compound
lemma grad_softplus {shape : S} (k : T shape → ℝ) (θ : T shape) :
  ∇ (λ θ, k (softplus θ)) θ = ∇ k (softplus θ) / (1 + exp (- θ)) :=
have H : (exp θ) / (exp θ + 1) = 1 / (1 + exp (- θ)), from
calc  (exp θ) / (exp θ + 1)
    = ((exp θ) / (exp θ + 1)) * ((exp θ)⁻¹ / (exp θ)⁻¹) : by simp [T.div_self (inv_pos (@exp_pos _ θ))]
... = ((exp θ * (exp θ)⁻¹) / ((exp θ + 1) * (exp θ)⁻¹)) : by simp [T.div_mul_div]
... = (1 / ((exp θ + 1) * (exp θ)⁻¹)) : by simp only [T.mul_inv_cancel (@exp_pos _ θ)]
... = 1 / ((exp θ * (exp θ)⁻¹) + 1 * (exp θ)⁻¹) : by simp only [right_distrib]
... = 1 / (1 + exp (- θ)) : by { simp only [T.mul_inv_cancel (@exp_pos _ θ), one_mul], rw exp_inv},

calc  ∇ (λ θ, k (softplus θ)) θ
    = ∇ (λ θ, k (log (exp θ + 1))) θ : rfl
... = ∇ (λ θ, k (log (θ + 1))) (exp θ) * exp θ : by rw T.grad_exp (λ θ, k (log (θ + 1)))
... = ∇ (λ θ, k (log θ)) (exp θ + 1) * exp θ : by rw T.grad_add₁ (λ θ, k (log θ))
... = ∇ k (log (exp θ + 1)) / (exp θ + 1) * exp θ : by rw (T.grad_log k (exp θ + 1) (plus_one_pos exp_pos))
... = ∇ k (softplus θ) * (exp θ / (exp θ + 1)) : by { rw [-T.mul_div_mul], reflexivity }
... = ∇ k (softplus θ) * (1 / (1 + exp (- θ))) : by rw H
... = ∇ k (softplus θ) / (1 + exp (- θ)) : by simp [T.one_div_inv, T.div_mul_inv]

lemma grad_sigmoid {shape : S} (k : T shape → ℝ) (θ : T shape) :
  ∇ (λ θ, k (sigmoid θ)) θ = ∇ k (sigmoid θ) * sigmoid θ * (1 - sigmoid θ) :=
have H_pre : 1 + exp (- θ) > 0, from one_plus_pos exp_pos,
have H : exp (- θ) / (1 + exp (- θ)) = 1 - sigmoid θ, from
calc  exp (- θ) / (1 + exp (- θ))
    = ((1 + exp (- θ)) - 1) / (1 + exp (- θ)) : by simp [sub_add_eq_sub_sub]
... = ((1 + exp (- θ)) / (1 + exp (- θ))) - 1 / (1 + exp (- θ)) : by simp [T.div_sub_div_same]
... = 1 - sigmoid θ : by { rw T.div_self (one_plus_pos exp_pos), reflexivity },

calc  ∇ (λ θ, k (sigmoid θ)) θ
    = ∇ (λ θ, k (1 / (1 + exp (- θ)))) θ : rfl
... = - ∇ (λ θ, k (1 / (1 + exp θ))) (- θ) : by rw T.grad_neg (λ θ, k (1 / (1 + exp θ)))
... = - (∇ (λ θ, k (1 / (1 + θ))) (exp (- θ)) * exp (- θ)) : by rw T.grad_exp (λ θ, k (1 / (1 + θ)))
... = - (∇ (λ θ, k (1 / θ)) (1 + exp (- θ)) * exp (- θ)) : by rw T.grad_add₂ (λ θ, k (1 / θ))
... = -(-(∇ k (1 / (1 + exp (-θ))) * 1) / square (1 + exp (-θ)) * exp (-θ)) : by rw (T.grad_div₂ k 1 (1 + exp (- θ)) (square_pos_of_pos $ one_plus_pos exp_pos))
... = (∇ k (1 / (1 + exp (-θ)))) / square (1 + exp (-θ)) * exp (-θ) : begin rw T.neg_div, simp [mul_neg_eq_neg_mul_symm] end
... = (∇ k (sigmoid θ)) / square (1 + exp (-θ)) * exp (-θ) : rfl
... = (∇ k (sigmoid θ)) * (1 / (1 + exp (-θ))) * (exp (-θ) / (1 + exp (- θ))) : by simp [square, T.div_mul_inv, T.mul_inv_pos H_pre H_pre]
... = (∇ k (sigmoid θ)) * sigmoid θ * (exp (-θ) / (1 + exp (- θ))) : rfl
... = ∇ k (sigmoid θ) * sigmoid θ * (1 - sigmoid θ) : by rw H

-- Gradients wrt arbitrary functions
lemma grad_add_fs {ishape : S} (θ : T ishape) (f₁ f₂ : T ishape → ℝ) :
  is_cdifferentiable f₁ θ → is_cdifferentiable f₂ θ →
  ∇ (λ θ₀, f₁ θ₀ + f₂ θ₀) θ = ∇ (λ θ₀, f₁ θ₀) θ + ∇ (λ θ₀, f₂ θ₀) θ :=
assume H_f₁ H_f₂,
have H₁ : is_cdifferentiable (λ θ₀, f₁ θ₀ + f₂ θ) θ,
  begin apply iff.mp (is_cdifferentiable_add_fs _ _ _), split, exact H_f₁, apply is_cdifferentiable_const end,

have H₂ : is_cdifferentiable (λ θ₀, f₁ θ + f₂ θ₀) θ,
  begin apply iff.mp (is_cdifferentiable_add_fs _ _ _), split, apply is_cdifferentiable_const, exact H_f₂ end,

begin
rw grad_binary (λ θ₁ θ₂, f₁ θ₁ + f₂ θ₂) _ H₁ H₂,
rw [grad_chain_rule _ (λ θ₀, θ₀ + f₂ θ) θ, grad_chain_rule _ (λ θ₀, f₁ θ + θ₀) θ],
rw [tmulT_scalar, D_scalar, tmulT_scalar, D_scalar],
rw [grad_add₁ (λ θ, θ), grad_id, one_smul],
rw [grad_add₂ (λ θ, θ), grad_id, one_smul]
end

lemma grad_scale_f {ishape : S} (θ : T ishape) (α : ℝ) (f : T ishape → ℝ) :
  ∇ (λ θ₀, α ⬝ f θ₀) θ = α ⬝ ∇ (λ θ₀, f θ₀) θ :=
begin
rw grad_chain_rule f (λ θ, α ⬝ θ) θ,
rw grad_scale (λ θ, θ),
rw grad_id,
rw smul.def,
rw mul_one,
rw tmulT_scalar,
rw D_scalar,
dunfold smul has_smul.smul scalar_mul,
rw const_scalar
end

lemma grad_log_f {shape : S} (θ : T shape) (f : T shape → ℝ) : f θ > 0 → ∇ (λ θ₀, log (f θ₀)) θ = (f θ)⁻¹ ⬝ ∇ f θ :=
assume H_pos,
have H_grad_log_simple : Π {θ : ℝ}, θ > 0 → ∇ log θ = θ⁻¹, from
begin
intros θ H_pos,
rw grad_log (λ θ, θ) _ H_pos,
rw grad_id,
apply T.one_div_inv
end,
by rw [grad_chain_rule, tmulT_scalar, D_scalar, H_grad_log_simple H_pos]

section simplify_grad
open list expr tactic

lemma id_rule {A : Type*} (a : A) : id a = a := rfl

meta def reduce_k (k : expr) : tactic expr :=
do slss ← simp_lemmas.add_simp simp_lemmas.mk `certigrad.T.id_rule,
   slss^.dsimplify k <|> return k

meta def has_x (x e : expr) : bool := expr.fold e ff (λ (m : expr) (d : nat) (b : bool), if m = x then tt else b)

meta def compute_outer_inner_functions_core (x : expr) : Π (k e : expr), tactic expr :=
λ (k e :  expr),
do let f := get_app_fn e,
   let args := get_app_args e,
   let n := length args,
   let barg₁ := dnth args (n-2),
   let barg₂ := dnth args (n-1),
   barg₁_type ← infer_type barg₁,
   barg₂_type ← infer_type barg₂,
   if barg₁ = x ∨ barg₂ = x
     then return k
     else if has_x x barg₁
          then compute_outer_inner_functions_core (lam `x binder_info.default barg₁_type (app k $ mk_app f $ update_nth args (n-2) (var 0))) barg₁
          else if has_x x barg₂
               then compute_outer_inner_functions_core (lam `x binder_info.default barg₂_type (app k $ mk_app f $ update_nth args (n-1) (var 0))) barg₂
               else tactic.fail "no var0"

meta def compute_outer_inner_functions (grad : expr) : tactic expr :=
let g := app_arg (app_fn grad) in
do f ← head_eta_expand g,
   x ← mk_local_def `x (binding_domain f),
   body ← return (instantiate_var (binding_body f) x),
   body_type ← infer_type body,
   initial_k ← return (lam `x binder_info.default body_type (var 0)),
   compute_outer_inner_functions_core x initial_k body <|> return initial_k

meta def compute_k (grad : expr) : tactic expr :=
do k ← compute_outer_inner_functions grad,
   k_simp ← reduce_k k,
   head_eta_expand k_simp

meta def check_grad (e : expr) : tactic expr :=
if is_napp_of e `certigrad.T.grad 3 then head_eta_expand e else tactic.fail "not ∇"

meta def try_add_simp (s : simp_lemmas) (p : pexpr) : tactic simp_lemmas :=
do oe ← try_core $ to_expr p,
   match oe with
   | none := return s
   | (some e) := simp_lemmas.add s e
   end

meta def build_simplify_grad_simp_lemmas (k : expr) : tactic simp_lemmas :=
do es ← monad.mapm to_expr
                   [``(@certigrad.T.grad_const)
                  , ``(@certigrad.T.grad_id)
                  , ``(@certigrad.T.grad_scale_f)
                  , ``(certigrad.T.grad_exp %%k)
                  , ``(certigrad.T.grad_log %%k)
                  , ``(certigrad.T.grad_scale %%k)
                  , ``(certigrad.T.grad_neg %%k)
                  , ``(certigrad.T.grad_add₁ %%k)
                  , ``(certigrad.T.grad_add₂ %%k)
                  , ``(certigrad.T.grad_sub₁ %%k)
                  , ``(certigrad.T.grad_sub₂ %%k)
                  , ``(certigrad.T.grad_mul₁ %%k)
                  , ``(certigrad.T.grad_mul₂ %%k)
                  , ``(certigrad.T.grad_div₁ %%k)
                  , ``(certigrad.T.grad_div₂ %%k)
                  , ``(@certigrad.T.grad_dot₁)
                  , ``(@certigrad.T.grad_dot₂)
                  , ``(certigrad.T.grad_square %%k)
                  , ``(certigrad.T.grad_softplus %%k)
                  , ``(certigrad.T.grad_sigmoid %%k)
],
   s ← simp_lemmas.append simp_lemmas.mk es,
   -- These have shape requirements that may cause `to_expr` to fail
   s ← try_add_simp s ``(certigrad.T.grad_gemm₁ %%k),
   s ← try_add_simp s ``(certigrad.T.grad_gemm₂ %%k),
   s ← try_add_simp s ``(certigrad.T.grad_sum %%k),
   -- These haven't been defined yet
   s ← try_add_simp s ```(certigrad.T.grad_mvn_iso_kl₁ %%k),
   s ← try_add_simp s ```(certigrad.T.grad_mvn_iso_kl₂ %%k),
   s ← try_add_simp s ```(certigrad.T.grad_bernoulli_neglogpdf₁ %%k),
   s ← try_add_simp s ```(certigrad.T.grad_bernoulli_neglogpdf₂ %%k),
   return s

meta def prove_preconditions_core : tactic unit :=
first (assumption :: map applyc [`certigrad.T.sqrt_pos, `certigrad.T.square_pos_of_pos, `certigrad.T.exp_pos,
                                 `certigrad.T.sigmoid_pos, `certigrad.T.sigmoid_lt1, `certigrad.T.lt1_alt, `certigrad.T.one_plus_pos,
                                 `certigrad.T.plus_one_pos, `certigrad.T.one_pos, `certigrad.T.neg_of_pos, `certigrad.T.const_pos_of_pos,
                                 `certigrad.T.mul_pos_of_pos_pos, `certigrad.T.pi_pos,
                                 `certigrad.T.inv_pos, `certigrad.T.div_pos_pos, `certigrad.T.two_pos, `certigrad.T.two_pi_pos])

meta def prove_preconditions : tactic unit := repeat prove_preconditions_core

meta def simplify_grad_core_helper (tac : tactic unit) : conv unit :=
λ r e, do guard $ r = `eq,
          grad ← check_grad e,
          k ← compute_k grad,
          s ← build_simplify_grad_simp_lemmas k,
          conv.apply_lemmas_core s tac r e

meta def simplify_grad_core (tac : tactic unit) : tactic unit :=
at_target (λ e, do (a, new_e, pf) ← ext_simplify_core () {zeta := ff, beta := ff, eta := ff, proj := ff} simp_lemmas.mk
                                                      (λ u, failed)
                                                      (λ a s r p e, failed)
                                                      (λ a s r p e, do ⟨u, new_e, pr⟩ ← simplify_grad_core_helper tac r e,
                                                                       return ((), new_e, pr, tt))
                                                      `eq e,
                return (new_e, pf))

meta def check_is_cdifferentiable (e : expr) : tactic expr :=
if is_napp_of e `certigrad.T.is_cdifferentiable 3 then head_eta_expand e else tactic.fail "not is_cdifferentiable"

meta def prove_differentiable_core (grad : expr) : tactic unit :=
do k ← compute_k grad,
   first [applyc `certigrad.T.is_cdifferentiable_const
        , applyc `certigrad.T.is_cdifferentiable_id
          -- these haven't been defined yet
        , to_expr ```(T.is_cdifferentiable_sigmoid %%k) >>= apply
        , to_expr ```(T.is_cdifferentiable_softplus %%k) >>= apply
        , to_expr ```(T.is_cdifferentiable_mvn_iso_kl₁ %%k) >>= apply
        , to_expr ```(T.is_cdifferentiable_mvn_iso_kl₂ %%k) >>= apply
        , to_expr ```(T.is_cdifferentiable_bernoulli_neglogpdf₁ %%k) >>= apply
        , to_expr ```(T.is_cdifferentiable_bernoulli_neglogpdf₂ %%k) >>= apply

        , to_expr ``(T.is_cdifferentiable_exp %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_log %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_sqrt %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_scale %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_neg %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_inv %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_add₁ %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_add₂ %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_sub₁ %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_sub₂ %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_mul₁ %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_mul₂ %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_div₁ %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_div₂ %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_square %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_sum %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_prod %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_gemm₁ %%k) >>= apply
        , to_expr ``(T.is_cdifferentiable_gemm₂ %%k) >>= apply
]

meta def prove_differentiable : tactic unit := repeat ((target >>= check_is_cdifferentiable >>= prove_differentiable_core) <|> prove_preconditions_core)

meta def simplify_grad : tactic unit := simplify_grad_core (prove_preconditions <|> prove_differentiable)
end simplify_grad

-- Compounds with simplify_grad

lemma grad_mvn_iso_kl₁ (k : ℝ → ℝ) (shape : S) (μ σ : T shape) : ∇ (λ μ, k (mvn_iso_kl μ σ)) μ = ∇ k (mvn_iso_kl μ σ) ⬝ μ :=
begin
dunfold T.mvn_iso_kl,
simplify_grad,
simp [T.smul.def, T.const_neg, T.const_mul, T.const_zero, T.const_one, T.const_bit0, T.const_bit1, T.const_inv],
rw [-(mul_assoc (2 : T shape) 2⁻¹), T.mul_inv_cancel two_pos],
simp
end

lemma grad_mvn_iso_kl₂ (k : ℝ → ℝ) (shape : S) (μ σ : T shape) (H_σ : σ > 0) (H_k : is_cdifferentiable k (mvn_iso_kl μ σ)) :
  ∇ (λ σ, k (mvn_iso_kl μ σ)) σ = ∇ k (mvn_iso_kl μ σ) ⬝ (σ - (1 / σ)) :=
have H_σ₂ : square σ > 0, from square_pos_of_pos H_σ,
have H_diff₁ : is_cdifferentiable (λ (θ₀ : T shape), k (-2⁻¹ * T.sum (1 + T.log (square θ₀) - square μ - square σ))) σ, by prove_differentiable,
have H_diff₂ : is_cdifferentiable (λ (θ₀ : T shape), k (-2⁻¹ * T.sum (1 + T.log (square σ) - square μ - square θ₀))) σ, by prove_differentiable,

begin
dunfold T.mvn_iso_kl,
rw (T.grad_binary (λ θ₁ θ₂, k ((- 2⁻¹) * T.sum (1 + T.log (square θ₁) - square μ - square θ₂))) _ H_diff₁ H_diff₂),
dsimp,
simplify_grad,
simp [T.smul.def, T.const_neg, T.const_mul, T.const_zero,
      T.const_one, T.const_bit0, T.const_bit1, T.const_inv,
      left_distrib, right_distrib],
rw [-(mul_assoc (2 : T shape) 2⁻¹), T.mul_inv_cancel two_pos],
erw T.neg_div,
simp [mul_neg_eq_neg_mul_symm, neg_mul_eq_neg_mul_symm],
apply congr_arg, apply congr_arg,
simp only [T.mul_div_mul, square],
rw [-mul_assoc, T.mul_div_mul, (@T.div_self_square _ σ H_σ)],
simp,
rw [-(mul_assoc (2 : T shape) 2⁻¹), T.mul_inv_cancel two_pos],
simp,
rw T.div_mul_inv,
simp
end

lemma grad_bernoulli_neglogpdf₁ (k : ℝ → ℝ) (shape : S) (p z : T shape)
                                (H_p₁ : 0 < p) (H_p₂ : 0 < 1 - p) (H_k : is_cdifferentiable k (bernoulli_neglogpdf p z)) :
  ∇ (λ p, k (bernoulli_neglogpdf p z)) p = ∇ k (bernoulli_neglogpdf p z) ⬝ ((1 - z) / (1 - p) - z / p) :=
have H_diff₁ : is_cdifferentiable (λ (θ₀ : T shape), k (-T.sum (z * T.log θ₀ + (1 - z) * T.log (1 - p)))) p, by prove_differentiable,
have H_diff₂ : is_cdifferentiable (λ (θ₀ : T shape), k (-T.sum (z * T.log p + (1 - z) * T.log (1 - θ₀)))) p, by prove_differentiable,

begin
dunfold T.bernoulli_neglogpdf,
rw T.grad_binary (λ θ₁ θ₂, k ( - T.sum (z * T.log θ₁ + (1 - z) * T.log (1 - θ₂)))) _ H_diff₁ H_diff₂,
dsimp,
simplify_grad,
simp [T.smul.def, const_neg, T.neg_div, T.div_mul_inv, left_distrib, right_distrib],
end

lemma grad_bernoulli_neglogpdf₂ (k : ℝ → ℝ) (shape : S) (p z : T shape)
                                (H_p₁ : 0 < p) (H_p₂ : 0 < 1 - p) (H_k : is_cdifferentiable k (bernoulli_neglogpdf p z)) :
  ∇ (λ z, k (bernoulli_neglogpdf p z)) z = ∇ k (bernoulli_neglogpdf p z) ⬝ (log (1 - p) - log p) :=
have H_diff₁ : is_cdifferentiable (λ (θ₀ : T shape), k (-T.sum (θ₀ * T.log p + (1 - z) * T.log (1 - p)))) z, by prove_differentiable,
have H_diff₂ : is_cdifferentiable (λ (θ₀ : T shape), k (-T.sum (z * T.log p + (1 - θ₀) * T.log (1 - p)))) z, by prove_differentiable,

begin
dunfold T.bernoulli_neglogpdf,
rw T.grad_binary (λ θ₁ θ₂, k (- T.sum (θ₁ * T.log p + (1 - θ₂) * T.log (1 - p)))) _ H_diff₁ H_diff₂,
dsimp,
simplify_grad,
simp [T.smul.def, const_neg, left_distrib, right_distrib],
end

-- Compounds with prove_differentiable
lemma is_cdifferentiable_sigmoid {shape : S} (k : T shape → ℝ) (θ : T shape) :
  is_cdifferentiable k (sigmoid θ) → is_cdifferentiable (λ θ, k (sigmoid θ)) θ :=
begin intro H, dunfold sigmoid, prove_differentiable end

lemma is_cdifferentiable_softplus {shape : S} (k : T shape → ℝ) (θ : T shape) :
  is_cdifferentiable k (softplus θ) → is_cdifferentiable (λ θ, k (softplus θ)) θ :=
begin intro H, dunfold softplus, prove_differentiable end

lemma is_cdifferentiable_mvn_iso_kl₁ (k : ℝ → ℝ) (shape : S) (μ σ : T shape) :
  is_cdifferentiable k (mvn_iso_kl μ σ) → is_cdifferentiable (λ μ, k (mvn_iso_kl μ σ)) μ :=
begin intro H, dunfold mvn_iso_kl, prove_differentiable end

lemma is_cdifferentiable_mvn_iso_kl₂ (k : ℝ → ℝ) (shape : S) (μ σ : T shape) (H_σ : σ > 0) :
  is_cdifferentiable k (mvn_iso_kl μ σ) → is_cdifferentiable (λ σ, k (mvn_iso_kl μ σ)) σ :=
begin
intro H, dunfold mvn_iso_kl,
apply is_cdifferentiable_binary (λ θ₁ θ₂, k (-2⁻¹ * T.sum (1 + T.log (square θ₁) + -square μ + -square θ₂))),
{ dsimp, prove_differentiable },
{ dsimp, prove_differentiable }
 end

lemma is_cdifferentiable_bernoulli_neglogpdf₁ (k : ℝ → ℝ) (shape : S) (p z : T shape) (H_p₁ : p > 0) (H_p₂ : p < 1) :
  is_cdifferentiable k (bernoulli_neglogpdf p z) → is_cdifferentiable (λ p, k (bernoulli_neglogpdf p z)) p :=
begin
intro H, dunfold bernoulli_neglogpdf,
apply is_cdifferentiable_binary (λ θ₁ θ₂, k (-T.sum (z * T.log θ₁ + (1 + -z) * T.log (1 + -θ₂)))),
{ dsimp, prove_differentiable },
{ dsimp, prove_differentiable }
end

lemma is_cdifferentiable_bernoulli_neglogpdf₂ (k : ℝ → ℝ) (shape : S) (p z : T shape) :
  is_cdifferentiable k (bernoulli_neglogpdf p z) → is_cdifferentiable (λ z, k (bernoulli_neglogpdf p z)) z :=
begin
intro H, dunfold bernoulli_neglogpdf,
apply is_cdifferentiable_binary (λ θ₁ θ₂, k (-T.sum (θ₁ * T.log p + (1 + -θ₂) * T.log (1 + -p)))),
{ dsimp, prove_differentiable },
{ dsimp, prove_differentiable }
end

-- Random

lemma mvn_iso_grad_logpdf_μ_correct {shape : S} (μ σ x : T shape) (H_σ : σ > 0) :
  ∇ (λ θ, mvn_iso_logpdf θ σ x) μ = mvn_iso_grad_logpdf_μ μ σ x :=
begin
dunfold mvn_iso_logpdf,
note H := square_pos_of_pos H_σ,
simplify_grad,
simp [smul.def, const_bit0, const_one, const_neg, const_inv, T.neg_div],
rw -mul_assoc, rw T.mul_inv_cancel two_pos,
simp, rw T.div_div_eq_div_mul,
reflexivity
end

lemma mvn_iso_grad_logpdf_σ_correct {shape : S} (μ σ x : T shape) (H_σ : σ > 0) :
  ∇ (λ θ, mvn_iso_logpdf μ θ x) σ = mvn_iso_grad_logpdf_σ μ σ x :=
have H_σ₂ : square σ > 0, from square_pos_of_pos H_σ,
have H_d₁ : is_cdifferentiable (λ θ₀, -2⁻¹ * sum (square ((x - μ) / θ₀) + log (2 * pi shape) + log (square σ))) σ, by prove_differentiable,
have H_d₂ : is_cdifferentiable (λ θ₀, -2⁻¹ * sum (square ((x - μ) / σ) + log (2 * pi shape) + log (square θ₀))) σ, by prove_differentiable,

have H₁ : (2 * (2⁻¹ / square σ)) = σ⁻¹ * σ⁻¹,
  begin dunfold square, rw [T.mul_div_mul_alt, T.mul_inv_cancel two_pos, one_div_inv, T.mul_inv_pos H_σ H_σ] end,

have H₂ : 2 * ((x + -μ) * ((x + -μ) * 2⁻¹)) = (2 * 2⁻¹) * square (x - μ), by simp [square],

begin
dunfold mvn_iso_logpdf,
rw grad_binary (λ θ₁ θ₂, -2⁻¹ * sum (square ((x - μ) / θ₁) + log (2 * pi shape) + log (square θ₂))) _ H_d₁ H_d₂, dsimp,
simplify_grad,
simp [smul.def, const_bit0, const_one, const_neg, const_inv, T.neg_div, T.div_div_eq_div_mul],
rw H₁,
rw -mul_assoc, rw T.mul_inv_cancel H_σ,
simp [T.mul_div_mul_alt, T.div_div_eq_div_mul],
rw [H₂, T.mul_inv_cancel two_pos],
simp [mvn_iso_grad_logpdf_σ]
end

-- With data structures
lemma grad_sumr {X : Type} {shape : S} (θ : T shape) (f : T shape → X → ℝ) :
  Π (xs : list X),
    is_cdifferentiable (λ (θ₀ : T shape), sumr (map (f θ₀) xs)) θ →
    ∇ (λ (θ₀ : T shape), list.sumr (map (f θ₀) xs)) θ
    =
    list.sumr (map (λ x, ∇ (λ θ₀, f θ₀ x) θ) xs)
| []      H_diff := by { dunfold map sumr, rw grad_const }
| (x::xs) H_diff :=
begin
dunfold map sumr,
dunfold map sumr at H_diff,

rw grad_add_fs _ _ _ (iff.mpr (is_cdifferentiable_add_fs _ _ _) H_diff)^.left (iff.mpr (is_cdifferentiable_add_fs _ _ _) H_diff)^.right,
rw grad_sumr _ (iff.mpr (is_cdifferentiable_add_fs _ _ _) H_diff)^.right
end

-- Note: this could be proved from a `select`/`replicate` formulation,
-- but it is arguably a more natural way of axiomatizing the property anyway.
axiom multiple_args_general :
  ∀ (parents : list reference) (tgt : reference) (m : env)
    (f : dvec T parents^.p2 → T tgt.2 → ℝ) (θ : T tgt.2),
    is_cdifferentiable (λ θ₀, f (env.get_ks parents (env.insert tgt θ m)) θ₀) θ →
    is_cdifferentiable (λ θ₀, sumr (map (λ (idx : ℕ), f (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ m)) idx) θ)
                                       (filter (λ idx, tgt = dnth parents idx) (riota $ length parents)))) θ →
∇ (λ (θ₀ : T tgt.2), f (env.get_ks parents (env.insert tgt θ₀ m)) θ₀) θ
=
∇ (λ θ₀, f (env.get_ks parents (env.insert tgt θ m)) θ₀) θ +
sumr (map (λ (idx : ℕ),
            ∇ (λ θ₀, f (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ m)) idx) θ) θ)
         (filter (λ idx, tgt = dnth parents idx) (riota $ length parents)))

end T
end certigrad
