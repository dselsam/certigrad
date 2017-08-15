/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Miscellaneous facts and theorems about tensors.

We view tensors as a field extended component-wise.  As such, they
form an ordered (but not linearly-ordered) commutative ring.  They
also have division, except the precondition for cancellation is not `x
≠ 0` but `|x| > 0`, which we simplify to `x > 0`.

Note: the axioms are by no means minimal.
-/
import .tensor .id .reference .env .dvec

-- TODO(dhs): move these elsewhere once #1659 is resolved.
attribute [congr] dif_ctx_simp_congr
attribute [simp] dif_pos dif_neg

namespace certigrad

namespace T
open list

axiom const_scalar : ∀ (α : ℝ), const α [] = α
attribute [simp] const_scalar

axiom const_mul {shape : S} : Π (α β : ℝ), const (α * β) shape = const α shape * const β shape
axiom const_neg {shape : S} : Π (α : ℝ), const (- α) shape = - const α shape
axiom const_inv {shape : S} : Π (α : ℝ), const α⁻¹ shape = (const α shape)⁻¹

axiom const_zero {shape : S} : const 0 shape = 0
axiom const_one {shape : S} : const 1 shape = 1
axiom const_bit0 {shape : S} : Π (α : ℝ), const (bit0 α) shape = bit0 (const α shape)
axiom const_bit1 {shape : S} : Π (α : ℝ), const (bit1 α) shape = bit1 (const α shape)

--attribute [simp] const_mul const_neg const_inv const_zero const_one const_bit0 const_bit1

-- Module structure
axiom smul.def (α : ℝ) (shape : S) (x : T shape) : α ⬝ x = const α shape * x
axiom smul_neg (α : ℝ) : ∀ {shape : S} (x : T shape), α ⬝ (- x) = - (α ⬝ x)
axiom smul_addr (α : ℝ) : ∀ (shape : S) (x y : T shape), α ⬝ (x + y) = α ⬝ x + α ⬝ y
axiom smul_addl (α β : ℝ) : ∀ (shape : S) (x : T shape), (α + β) ⬝ x = α ⬝ x + β ⬝ x
axiom smul_group (α β : ℝ) : ∀ (shape : S) (x : T shape), (α * β) ⬝ x = α ⬝ (β ⬝ x)
axiom smul_flip (α β : ℝ) : ∀ (shape : S) (x : T shape), α ⬝ (β ⬝ x) = β ⬝ (α ⬝ x)
axiom one_smul : ∀ (shape : S) (x : T shape), (1 : ℝ) ⬝ x = x

axiom smul_zero (α : ℝ) : ∀ (shape : S), α ⬝ (0 : T shape) = 0
axiom zero_smul : ∀ (shape : S) (x : T shape), (0 : ℝ) ⬝ x = 0
axiom smul_mul_scalar_right (α : ℝ) : ∀ (x y : ℝ), α ⬝ (x * y) = x ⬝ (α ⬝ y)
axiom smul_mul₁ (α : ℝ) : ∀ {shape : S} (x y : T shape), y * (α ⬝ x) = α ⬝ (x * y)
axiom smul_mul₂ (α : ℝ) : ∀ {shape : S} (x y : T shape), (α ⬝ x) * y = α ⬝ (x * y)
axiom smul_comm (α β : ℝ) : α ⬝ β = β ⬝ α
axiom smul_sum {shape : S} (α : ℝ) (x : T shape) : α ⬝ sum x = sum (α ⬝ x)
axiom smul_div {shape : S} (α : ℝ) (x y : T shape) : α ⬝ (x / y) = (α ⬝ x) / y
axiom smul_scale : ∀ (α : ℝ) (shape : S) (x : T shape), (α ⬝ 1) * x = α ⬝ x
axiom smul_scalar : ∀ (α x : ℝ), (α ⬝ x) = α * x

-- sum
axiom sum_empty_vec (x : T [0]) : sum x = 0
axiom sum_mat_no_cols {nrows : ℕ} (x : T [nrows, 0]) : sum x = 0
axiom sum_zero : Π {shape : S}, sum (0 : T shape) = 0
axiom sum_add {shape : S} (x y : T shape) : sum (x + y) = sum x + sum y
axiom sum_neg {shape : S} (x : T shape) : sum (- x) = - (sum x)
axiom sum_smul {shape : S} (α : ℝ) (x : T shape) : sum (α ⬝ x) = α * sum x

-- Misc
axiom sqrt_mul {shape : S} : ∀ (x y : T shape), sqrt (x * y) = sqrt x * sqrt y
axiom sqrt_square {shape : S} : ∀ (x : T shape), sqrt (square x) = x
axiom prod_mul {shape : S} : ∀ (x y : T shape), prod (x * y) = prod x * prod y
axiom mul_inv_pos {shape : S} : ∀ {x y : T shape}, x > 0 → y > 0 → (x * y)⁻¹ = x⁻¹ * y⁻¹
axiom inv_mul_cancel {shape : S} : ∀ {x : T shape}, x > 0 → (x⁻¹ * x) = 1
axiom mul_inv_cancel {shape : S} : ∀ {x : T shape}, x > 0 → (x * x⁻¹) = 1
axiom div_one {shape : S} : ∀ {x : T shape}, x / 1 = x
axiom log_one {shape : S} : log (1 : T shape) = (0 : T shape)
axiom log_const {shape : S} (α : ℝ) : log (const α shape) = const (log α) shape
axiom exp_inv {shape : S} (x : T shape) : (exp x)⁻¹ = exp (- x)
axiom neg_div : ∀ {shape : S} {x y : T shape}, -x / y = -(x / y)
axiom log_prod : ∀ {shape : S} {x : T shape}, x > 0 → log (prod x) = sum (log x)
axiom log_mul : ∀ {shape : S} {x y : T shape}, x > 0 → y > 0 → log (x * y) = log x + log y
axiom log_exp : ∀ {shape : S} {x : T shape}, log (exp x) = x
axiom log_sqrt : ∀ {shape : S} {x : T shape}, log (sqrt x) = 2⁻¹ * log x
axiom log_inv : ∀ {shape : S} {x : T shape}, log (x⁻¹) = - log x

-- Signs
axiom nz_of_pos {shape : S} : ∀ {x : T shape}, x > 0 → x ≠ 0
axiom nz_of_div {shape : S} : ∀ {x y : T  shape}, x ≠ 0 → y ≠ 0 → x / y ≠ 0
axiom nz_iff {shape : S} : ∀ {x : T shape}, x ≠ 0 ↔ x > 0 ∨ x < 0
axiom nneg_of_pos {shape : S} : ∀ {x : T shape}, x > 0 → x ≥ 0
axiom sqrt_pos {shape : S} : ∀ {x : T shape}, x > 0 → sqrt x > 0
axiom pos_of_sqrt_pos {shape : S} : ∀ {x : T shape}, sqrt x > 0 → x > 0
axiom square_nneg {shape : S} : ∀ {x : T shape}, square x ≥ 0
axiom square_pos_of_pos {shape : S} : ∀ {x : T shape}, 0 < x → 0 < square x
axiom square_pos_of_neg {shape : S} : ∀ {x : T shape}, x < 0 → 0 < square x
axiom exp_pos {shape : S} : ∀ {x : T shape}, exp x > 0
axiom sigmoid_pos {shape : S} : ∀ {x : T shape}, sigmoid x > 0
axiom sigmoid_lt1 {shape : S} : ∀ {x : T shape}, sigmoid x < 1
axiom lt1_alt {shape : S} : ∀ {x : T shape}, x < 1 → 0 < 1 - x
axiom one_plus_pos {shape : S} : ∀ {x : T shape}, x > 0 → 1 + x > 0
axiom one_plus_pos_iff {shape : S} : ∀ {x : T shape}, 0 < 1 + x ↔ (- 1 < x)
axiom plus_one_pos {shape : S} : ∀ {x : T shape}, x > 0 → x + 1 > 0
axiom one_pos {shape : S} : (1 : T shape) > 0
axiom neg_of_pos {shape : S} {x : T shape} : x > 0 → - x < 0
axiom const_pos_of_pos {shape : S} {x : ℝ} : x > 0 → const x shape > 0
axiom mul_pos_of_pos_pos {shape : S} {x y : T shape} : x > 0 → y > 0 → x * y > 0
axiom eps_pos {shape : S} : eps shape > 0
axiom pi_pos {shape : S} : pi shape > 0
axiom inv_pos {shape : S} {x : T shape} : x > 0 → x⁻¹ > 0
axiom div_pos_pos {shape : S} {x y : T shape} : x > 0 → y > 0 → x / y > 0
axiom add_pos_of_pos_pos {shape : S} {x y : T shape} : x > 0 → y > 0 → x + y > 0
lemma two_pos {shape : S} : (2 : T shape) > 0 := one_plus_pos one_pos
lemma two_pi_pos {shape : S} : 2 * pi shape > 0 := mul_pos_of_pos_pos two_pos pi_pos
lemma msigmoid_pos {shape : S} {x : T shape} : 0 < 1 - sigmoid x := lt1_alt sigmoid_lt1

-- div
axiom div_mul_cancel {shape : S} : ∀ {x y : T shape}, y > 0 → (x / y) * y = x
axiom div_div_eq_div_mul {shape : S} : ∀ (x y z : T shape), (x / y) / z = x / (y * z)
axiom div_mul_div {shape : S} : ∀ (x y z w : T shape), (x / y) * (z / w) = (x * z) / (y * w)
axiom mul_div_mul {shape : S} : ∀ (x y z : T shape), x * (y / z) = (x / z) * y
axiom mul_div_mul_alt {shape : S} : ∀ (x y z : T shape), x * (y / z) = (x * y / z)
axiom one_div_inv {shape : S} : ∀ (x : T shape), 1 / x = x⁻¹
axiom div_mul_inv {shape : S} : ∀ (x y : T shape), x / y = x * y⁻¹
axiom div_self {shape : S} : ∀ {x : T shape}, x > 0 → x / x = 1
axiom square_div {shape : S} : ∀ {x y : T shape}, square (x / y) = square x / square y

axiom div_add_div_same {shape : S} (x y z : T shape) : x / z + y / z = (x + y) / z
lemma div_add_div_same_symm {shape : S} (x y z : T shape) : (x + y) / z = x / z + y / z := by rw div_add_div_same
lemma div_sub_div_same {shape : S} (x y z : T shape) : x / z - y / z = (x - y) / z := by simp [T.div_add_div_same_symm, neg_div]
lemma div_sub_div_same_symm {shape : S} (x y z : T shape) : (x - y) / z = x / z - y / z := by rw div_sub_div_same
lemma div_self_square {shape : S} {x : T shape} (H_pos : x > 0) : x / (x * x)= x⁻¹ :=
calc  x / (x * x)
    = (x / x) / x : by rw -div_div_eq_div_mul
... = 1 / x : by rw div_self H_pos
... = x⁻¹ : by rw one_div_inv

-- integrable
axiom is_integrable_const : Π {shape₁ shape₂ : S} (c : T shape₂), is_integrable (λ (x : T shape₁), c)

lemma is_integrable_zero {shape₁ shape₂ : S} : is_integrable (λ (x : T shape₁), (0 : T shape₂)) := is_integrable_const (0 : T shape₂)

axiom is_integrable_scale : Π {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) (α : ℝ),
  is_integrable f ↔ is_integrable (λ x, α ⬝ f x)

axiom is_integrable_neg : Π {shape₁ shape₂ : S} (f : T shape₁ → T shape₂),
  is_integrable f ↔ is_integrable (λ x, - f x)

axiom is_integrable_div : Π {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) (y : T shape₂) (Hy : y > 0),
  is_integrable f ↔ is_integrable (λ x, (f x) / y)

axiom is_integrable_add : Π {shape₁ shape₂ : S} (f g : T shape₁ → T shape₂),
  (is_integrable f ∧ is_integrable g) ↔ is_integrable (λ x, f x + g x)

axiom is_integrable_tmulT {ishape oshape fshape : S} (M : T (ishape ++ oshape)) (f : T fshape → T oshape) :
  is_integrable f ↔ is_integrable (λ x, tmulT M (f x))

axiom is_integrable_sum : Π {shape₁ shape₂ : S} (f : T shape₁ → T shape₂),
  (is_integrable f) ↔ is_integrable (λ x, sum (f x))

axiom is_integrable_fscale : Π {shape₁ shape₂ : S} (f : T shape₁ → ℝ) (y : T shape₂),
  is_integrable f ↔ is_integrable (λ x, f x ⬝ y)

-- (provable)
axiom is_integrable_const_middle : Π {shape₁ shape₂ : S} (pdf : T shape₁ → ℝ) (c : T shape₂),
  is_integrable (λ (x : T shape₁), pdf x) ↔ is_integrable (λ (x : T shape₁), pdf x ⬝ c)

axiom is_integrable_add_middle : Π {shape₁ shape₂ : S} (pdf : T shape₁ → ℝ) (f g : T shape₁ → T shape₂),
  (is_integrable (λ (x : T shape₁), pdf x ⬝ f x) ∧ is_integrable (λ (x : T shape₁), pdf x ⬝ g x)) ↔ is_integrable (λ (x : T shape₁), pdf x ⬝ (f x + g x))

-- (provable)
axiom is_integrable_tmulT_middle {ishape oshape fshape : S} (M : T (ishape ++ oshape)) (pdf : T fshape → ℝ) (f : T fshape → T oshape) :
  is_integrable (λ (x : T fshape), pdf x ⬝ f x) ↔ is_integrable (λ (x : T fshape), pdf x ⬝ tmulT M (f x))

-- uniformly integrable
axiom is_uniformly_integrable_around_binary : Π {shape₁ shape₂ shape₃ : S} (f : T shape₁ → T shape₁ → T shape₂ → T shape₃) (θ : T shape₁),
  (is_uniformly_integrable_around (λ θ₀ x, f θ₀ θ x) θ ∧ is_uniformly_integrable_around (λ θ₀ x, f θ θ₀ x) θ) ↔ is_uniformly_integrable_around (λ θ₀ x, f θ₀ θ₀ x) θ

lemma uint_left {shape₁ shape₂ shape₃ : S} (f : T shape₁ → T shape₁ → T shape₂ → T shape₃) (θ : T shape₁) :
  is_uniformly_integrable_around (λ θ₀ x, f θ₀ θ₀ x) θ → is_uniformly_integrable_around (λ θ₀ x, f θ₀ θ x) θ :=
assume H_uint, (iff.mpr (is_uniformly_integrable_around_binary f θ) H_uint)^.left

lemma uint_right {shape₁ shape₂ shape₃ : S} (f : T shape₁ → T shape₁ → T shape₂ → T shape₃) (θ : T shape₁) :
  is_uniformly_integrable_around (λ θ₀ x, f θ₀ θ₀ x) θ → is_uniformly_integrable_around (λ θ₀ x, f θ θ₀ x) θ :=
assume H_uint, (iff.mpr (is_uniformly_integrable_around_binary f θ) H_uint)^.right

-- (provable)
axiom is_uniformly_integrable_around_binary_grad : Π {shape₁ shape₂ : S} (f₁ f₂ : T shape₁ → T shape₂ → ℝ) (θ : T shape₁),
  (∀ x, is_cdifferentiable (λ θ₀, f₁ θ₀ x) θ) → (∀ x, is_cdifferentiable (λ θ₀, f₂ θ₀ x) θ) →
  (is_uniformly_integrable_around (λ θ₀ x, f₂ θ₀ x ⬝ ∇ (λ θ₁, f₁ θ₁ x) θ₀) θ ∧ is_uniformly_integrable_around (λ θ₀ x, f₁ θ₀ x ⬝ ∇ (λ θ₁, f₂ θ₁ x) θ₀) θ ↔
   is_uniformly_integrable_around (λ θ₀ x, ∇ (λ θ₁, f₁ θ₁ x ⬝ f₂ θ₁ x) θ₀) θ)

lemma uint_grad_left {shape₁ shape₂ : S} (f₁ f₂ : T shape₁ → T shape₂ → ℝ) (θ : T shape₁) :
  (∀ x, is_cdifferentiable (λ θ₀, f₁ θ₀ x) θ) → (∀ x, is_cdifferentiable (λ θ₀, f₂ θ₀ x) θ) →
   is_uniformly_integrable_around (λ θ₀ x, ∇ (λ θ₁, f₁ θ₁ x ⬝ f₂ θ₁ x) θ₀) θ → is_uniformly_integrable_around (λ θ₀ x, f₂ θ₀ x ⬝ ∇ (λ θ₁, f₁ θ₁ x) θ₀) θ :=
assume H_cdiff₁ H_cdiff₂ H_uint_grad, (iff.mpr (is_uniformly_integrable_around_binary_grad f₁ f₂ θ H_cdiff₁ H_cdiff₂) H_uint_grad)^.left

lemma uint_grad_right {shape₁ shape₂ : S} (f₁ f₂ : T shape₁ → T shape₂ → ℝ) (θ : T shape₁) :
  (∀ x, is_cdifferentiable (λ θ₀, f₁ θ₀ x) θ) → (∀ x, is_cdifferentiable (λ θ₀, f₂ θ₀ x) θ) →
   is_uniformly_integrable_around (λ θ₀ x, ∇ (λ θ₁, f₁ θ₁ x ⬝ f₂ θ₁ x) θ₀) θ → is_uniformly_integrable_around (λ θ₀ x, f₁ θ₀ x ⬝ ∇ (λ θ₁, f₂ θ₁ x) θ₀) θ :=
assume H_cdiff₁ H_cdiff₂ H_uint_grad, (iff.mpr (is_uniformly_integrable_around_binary_grad f₁ f₂ θ H_cdiff₁ H_cdiff₂) H_uint_grad)^.right

-- integrals
axiom integral_scale : Π {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) (α : ℝ),
  ∫ (λ x, α ⬝ f x) = α ⬝ ∫ (λ x, f x)

axiom integral_neg : Π {shape₁ shape₂ : S} (f : T shape₁ → T shape₂),
  ∫ (λ x, - (f x)) = - ∫ (λ x, f x)

axiom integral_div : Π {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) (y : T shape₂),
  ∫ (λ x, (f x) / y) = ∫ (λ x, f x) / y

axiom integral_add : Π {shape₁ shape₂ : S} (f g : T shape₁ → T shape₂),
  is_integrable f → is_integrable g → ∫ (λ x, f x + g x) = ∫ (λ x, f x) + ∫ (λ x, g x)

axiom integral_fscale : Π {shape₁ shape₂ : S} (f : T shape₁ → ℝ) (y : T shape₂),
  ∫ (λ x, f x ⬝ y) = ∫ (λ x, f x) ⬝ y

axiom integral_pos : ∀ {shape₁ shape₂ : S} (f : T shape₁ → T shape₂), (∀ x, f x > 0) → ∫ (λ x, f x) > 0
axiom integral_nneg : ∀ {shape₁ shape₂ : S} (f : T shape₁ → T shape₂), (∀ x, f x ≥ 0) → ∫ (λ x, f x) ≥ 0

lemma integral_congr {shape₁ shape₂ : S} (f g : T shape₁ → T shape₂) (H_fg : ∀ x, f x = g x) : ∫ f = ∫ g :=
  show ∫ (λ x, f x) = ∫ (λ x, g x), by rw (funext H_fg)

axiom integral_sum : Π {shape₁ shape₂ : S} (f : T shape₁ → T shape₂), is_integrable f → ∫ (λ x, sum (f x)) = sum (∫ (λ x, f x))

axiom smul_tmulT {ishape oshape : S} (α : ℝ) (M : T (ishape ++ oshape)) (y : T oshape) :
  α ⬝ (tmulT M y) = tmulT M (α ⬝ y)

axiom integral_tmulT {ishape oshape fshape : S} (M : T (ishape ++ oshape)) (f : T fshape → T oshape) :
  ∫ (λ x, tmulT M (f x)) = tmulT M (∫ f)

axiom integral_continuous : ∀ {ishape tshape fshape : S} (f : T ishape → T tshape → T fshape) (θ : T tshape),
  (∀ x, is_continuous (f x) θ) → is_continuous (λ θ₀, ∫ (λ x₀, f x₀ θ₀)) θ

-- D

axiom tmulT_scalar {shape : S} : ∀ (x : T (shape ++ [])) (y : ℝ), tmulT x y = y ⬝ (eq.rec_on (append_nil shape) x)
axiom D_scalar {shape : S} (f : T shape → ℝ) (θ : T shape) : (eq.rec_on (append_nil shape) (D f θ) : T shape) = ∇ f θ

-- dintegral

lemma dintegral_pos {oshape : S} : Π {shapes : list S} {f : dvec T shapes → T oshape}, (∀ x, f x > 0) → dintegral (λ x, f x) > 0
| [] f H := by apply H

| (shape::shapes) f H :=
begin
dunfold dintegral,
apply integral_pos,
intro x,
apply dintegral_pos,
intro xs,
apply H,
end

lemma dintegral_scale {shape : S} (α : ℝ) : Π {shapes : list S} (f : dvec T shapes → T shape),
  dintegral (λ (xs : dvec T shapes), α ⬝ f xs) = α ⬝ dintegral (λ xs, f xs)
| [] f := rfl

| (ds::shapes) f :=
begin
dunfold dintegral,
simp [λ x, @dintegral_scale shapes (λ v, f (x ::: v))],
rw integral_scale,
end

lemma is_dintegrable_scale {oshape : S} : Π {shapes : list S} (f : dvec T shapes → T oshape) (α : ℝ),
  is_dintegrable f ↔ is_dintegrable (λ x, α ⬝ f x)
| [] f α := begin split, all_goals { intro, exact trivial } end
| (shape::shapes) f α :=
begin
dunfold dintegral is_dintegrable,
split,
{ intro Hf, split,
  { simp only [dintegral_scale], exact iff.mp (is_integrable_scale _ α) Hf^.left },
  { intro x, exact iff.mp (is_dintegrable_scale _ _) (Hf^.right x) } },
{ intro Hαf, split,
  { simp only [dintegral_scale] at Hαf, exact iff.mpr (is_integrable_scale _ α) Hαf^.left },
  { intro x, exact iff.mpr (is_dintegrable_scale _ _) (Hαf^.right x) } }
end

lemma dintegral_add {shape : S} : Π {shapes : list S} (f g : dvec T shapes → T shape),
  is_dintegrable f → is_dintegrable g →
  dintegral (λ (xs : dvec T shapes), f xs + g xs) = dintegral (λ (xs : dvec T shapes), f xs) + dintegral (λ (xs : dvec T shapes), g xs)
| [] f g Hf Hg := rfl

| (ds::shapes) f g Hf Hg :=
begin
dunfold dintegral,
simp [λ x, @dintegral_add shapes (λ v, f (x ::: v)) (λ v, g (x :::v)) (Hf^.right x) (Hg^.right x)],
rw integral_add _ _ Hf^.left Hg^.left
end

lemma dintegral_div {shape : S} : Π {shapes : list S} (f : dvec T shapes → T shape) (y : T shape),
  dintegral (λ (xs : dvec T shapes), (f xs) / y) = dintegral (λ (xs : dvec T shapes), f xs) / y
| [] f y := rfl

| (ds::shapes) f y :=
begin
dunfold dintegral,
simp [λ x, @dintegral_div shapes (λ v, f (x ::: v)) y],
rw integral_div
end

lemma dintegral_add_middle {shape : S} : Π {shapes : list S} (pdf : dvec T shapes → ℝ) (f g : dvec T shapes → T shape),
  is_dintegrable (λ xs, pdf xs ⬝ f xs) → is_dintegrable (λ xs, pdf xs ⬝ g xs) →
  dintegral (λ (xs : dvec T shapes), pdf xs ⬝ (f xs + g xs)) = dintegral (λ (xs : dvec T shapes), pdf xs ⬝ f xs) + dintegral (λ (xs : dvec T shapes), pdf xs ⬝ g xs)
| [] pdf f g Hf Hg := begin dunfold dintegral, apply smul_addr end

| (ds::shapes) pdf f g Hf Hg :=
begin
dunfold dintegral,
simp [λ x, @dintegral_add_middle shapes (λ v, pdf (x ::: v)) (λ v, f (x ::: v)) (λ v, g (x :::v)) (Hf^.right x) (Hg^.right x)],
rw integral_add _ _ Hf^.left Hg^.left
end

lemma dintegral_neg_middle {shape : S} : Π {shapes : list S} (pdf : dvec T shapes → ℝ) (f : dvec T shapes → T shape),
  dintegral (λ (xs : dvec T shapes), pdf xs ⬝ - (f xs)) = - dintegral (λ (xs : dvec T shapes), pdf xs ⬝ f xs)
| [] pdf f := begin dunfold dintegral, apply smul_neg end

| (ds::shapes) pdf f :=
begin
dunfold dintegral,
simp [λ x, @dintegral_neg_middle shapes (λ v, pdf (x ::: v)) (λ v, f (x ::: v))],
rw integral_neg
end

lemma dintegral_mul (α : ℝ) : Π {shapes : list S} (f : dvec T shapes → ℝ),
  dintegral (λ (xs : dvec T shapes), α * f xs) = α * dintegral (λ xs, f xs) :=
begin
intros shapes f,
rw -(const_scalar α),
simp [λ s x, eq.symm (smul.def α s x)],
simp [λ α f, eq.symm (smul_scalar α f)],
exact (dintegral_scale α f)
end

lemma dintegral_scale_middle  {shape : S} (α : ℝ) : Π {shapes : list S} (f : dvec T shapes → ℝ) (g : dvec T shapes → T shape),
  dintegral (λ (xs : dvec T shapes), f xs ⬝ (α ⬝ g xs)) = α ⬝ dintegral (λ xs, f xs ⬝ g xs)
| [] f g :=
begin
dunfold dintegral,
simp [T.smul.def, mul_comm],
end

| (ds::shapes) f g :=
begin
dunfold dintegral,
simp [λ x, @dintegral_scale_middle shapes (λ v, f (x ::: v)) (λ v, g (x ::: v))],
rw integral_scale,
end

lemma dintegral_mul_middle (α : ℝ) : Π {shapes : list S} (f : dvec T shapes → ℝ) (g : dvec T shapes → ℝ),
  dintegral (λ (xs : dvec T shapes), f xs ⬝ (α * g xs)) = α * dintegral (λ xs, f xs ⬝ g xs) :=
begin
intros shapes f g,
rw -(const_scalar α),
simp [λ s x, eq.symm (smul.def α s x)],
simp [λ xs, eq.symm (smul_scalar α (g xs))],
rw dintegral_scale_middle α f g,
simp [smul_scalar]
end

lemma dintegral_tmulT  {shape₁ shape₂ : S} (M : T (shape₁ ++ shape₂)) : Π {shapes : list S} (f : dvec T shapes → T shape₂),
  dintegral (λ (xs : dvec T shapes), tmulT M (f xs)) = tmulT M (dintegral (λ xs, f xs))
| []           f := rfl

| (ds::shapes) f :=
begin
dunfold dintegral,
simp [λ x, @dintegral_tmulT shapes (λ v, f (x ::: v))],
rw integral_tmulT
end

lemma dintegral_tmulT_middle {shape₁ shape₂ : S} (M : T (shape₁ ++ shape₂)) : Π {shapes : list S} (f : dvec T shapes → ℝ) (g : dvec T shapes → T shape₂),
  dintegral (λ (xs : dvec T shapes), f xs ⬝ (tmulT M (g xs))) = tmulT M (dintegral (λ xs, f xs ⬝ g xs)) :=
begin
intros shapes f g,
simp [smul_tmulT, dintegral_tmulT]
end

lemma dintegral_const_middle {yshape : S} :
  ∀ {shapes : list S} (pdf : dvec T shapes → ℝ) (H_pdf_pos : ∀ x, pdf x > 0) (H_pdf_int1 : dintegral pdf = 1) (y : T yshape),
    dintegral (λ (xs : dvec T shapes), pdf xs ⬝ y) = y
| [] pdf H_pdf_pos H_pdf_int1 y :=
begin
dunfold dintegral,
dunfold dintegral at H_pdf_int1,
rw H_pdf_int1,
rw one_smul
end

| (shape::shapes) pdf H_pdf_pos H_pdf_int1 y :=
let pdf' : T shape → dvec T shapes → ℝ := λ x (xs : dvec T shapes), pdf (x ::: xs) / dintegral (λ (xs : dvec T shapes), pdf (x ::: xs)) in
have H_dpos : ∀ (x : T shape), dintegral (λ (xs : dvec T shapes), pdf (x ::: xs)) > 0, from λ x, dintegral_pos (λ x, H_pdf_pos _),
have H_pdf'_pos : ∀ (x : T shape) (xs : dvec T shapes), pdf' x xs > 0, from
  assume (x : T shape) (xs : dvec T shapes),
  have H₁ : pdf (x ::: xs) > 0, by apply H_pdf_pos,
  T.div_pos_pos H₁ (H_dpos x),

have H_pdf'_int1 : ∀ (x : T shape), dintegral (pdf' x) = 1, from
  assume (x : T shape),
  begin dsimp, rw T.dintegral_div, exact div_self (H_dpos x) end,

have H_inner₁ : ∀ (x : T shape), dintegral (λ (v : dvec T shapes), pdf (x ::: v) ⬝ y)
                     = dintegral (λ (v : dvec T shapes), (pdf' x v * dintegral (λ (vs : dvec T shapes), pdf (x ::: vs))) ⬝ y), from
  assume (x : T shape),
  begin dsimp, apply congr_arg, apply funext, intro xs, rw (T.div_mul_cancel (H_dpos _)) end,

have H_inner₂ : ∀ x, dintegral (λ (v : dvec T shapes), (pdf' x v * dintegral (λ (vs : dvec T shapes), pdf (x ::: vs))) ⬝ y)
                     = dintegral (λ (vs : dvec T shapes), pdf (x ::: vs)) ⬝ dintegral (λ (v : dvec T shapes), pdf' x v ⬝ y), from
  assume (x : T shape),
  begin dsimp, simp [smul_group, dintegral_scale] end,
begin
dunfold dintegral,
simp [H_inner₁, H_inner₂, (λ x, @dintegral_const_middle shapes (pdf' x) (H_pdf'_pos x) (H_pdf'_int1 x)), integral_fscale],
change dintegral (λ (vs : dvec T (shape::shapes)), pdf vs) ⬝ y = y,
rw [H_pdf_int1, one_smul]
end

-- btw axioms

axiom is_btw_id {shape : S} : is_btw_exp₂ (λ (x : T shape), x)
axiom is_btw_const {shape₁ shape₂ : S} (y : T shape₂) : is_btw_exp₂ (λ (x : T shape₁), y)
axiom is_btw_sigmoid {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : is_btw_exp₂ (λ (x : T shape₁), sigmoid (f x))
axiom is_btw_softplus {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ (λ (x : T shape₁), softplus (f x))
axiom is_btw_sum {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ (λ (x : T shape₁), sum (f x))
axiom is_btw_log_sigmoid {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) (y : T shape₂) : y > 0 → is_btw_exp₂ f → 
  is_btw_exp₂ (λ (x : T shape₁), log (y + sigmoid (f x)))
axiom is_btw_log_1msigmoid {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) (y : T shape₂) : y > 0 → is_btw_exp₂ f → 
  is_btw_exp₂ (λ (x : T shape₁), log (y + (1 - sigmoid (f x))))

axiom is_btw_gemm {shape : S} {m n p : ℕ} (f : T shape → T [m, n]) (g : T shape → T [n, p]) :
  is_btw_exp₂ f → is_btw_exp₂ g → is_btw_exp₂ (λ x, gemm (f x) (g x))

axiom is_btw_transpose {shape : S} {m n : ℕ} (f : T shape → T [m, n]) :
  is_btw_exp₂ f → is_btw_exp₂ (λ x, transpose (f x))

axiom is_btw_neg {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ (λ x, - (f x))
axiom is_btw_inv {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ (λ x, (f x)⁻¹)
axiom is_btw_add {shape₁ shape₂ : S} (f g : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ g → is_btw_exp₂ (λ x, f x + g x)
axiom is_btw_mul {shape₁ shape₂ : S} (f g : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ g → is_btw_exp₂ (λ x, f x * g x)
axiom is_btw_sub {shape₁ shape₂ : S} (f g : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ g → is_btw_exp₂ (λ x, f x - g x)
axiom is_btw_div {shape₁ shape₂ : S} (f g : T shape₁ → T shape₂) : is_btw_exp₂ f → is_btw_exp₂ g → is_btw_exp₂ (λ x, f x / g x)

axiom is_btw_exp {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : is_sub_quadratic f → is_btw_exp₂ (λ x, exp (f x))

-- sub quadratic axioms

axiom is_sub_quadratic_id {shape : S} : is_sub_quadratic (λ (x : T shape), x)
axiom is_sub_quadratic_const {shape₁ shape₂ : S} (y : T shape₂) : is_sub_quadratic (λ (x : T shape₁), y)

axiom is_sub_quadratic_gemm {shape : S} {m n p : ℕ} (f : T shape → T [m, n]) (g : T shape → T [n, p]) :
  is_sub_quadratic f → is_sub_quadratic g → is_sub_quadratic (λ x, gemm (f x) (g x))

axiom is_sub_quadratic_transpose {shape : S} {m n : ℕ} (f : T shape → T [m, n]) :
  is_sub_quadratic f → is_sub_quadratic (λ x, transpose (f x))

axiom is_sub_quadratic_softplus {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : is_sub_quadratic f → is_sub_quadratic (λ x, softplus (f x))

axiom is_sub_quadratic_neg {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : is_sub_quadratic f → is_sub_quadratic (λ x, - (f x))
axiom is_sub_quadratic_mul₁ {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) (y : T shape₂) : is_sub_quadratic f → is_sub_quadratic (λ x, y * f x)
axiom is_sub_quadratic_mul₂ {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) (y : T shape₂) : is_sub_quadratic f → is_sub_quadratic (λ x, f x * y)

axiom is_sub_quadratic_add {shape₁ shape₂ : S} (f g : T shape₁ → T shape₂) : is_sub_quadratic f → is_sub_quadratic g → is_sub_quadratic (λ x, f x + g x)
axiom is_sub_quadratic_sub {shape₁ shape₂ : S} (f g : T shape₁ → T shape₂) : is_sub_quadratic f → is_sub_quadratic g → is_sub_quadratic (λ x, f x - g x)

-- is_bounded_btw_exp₂_around {shape₁ shape₂ shape₃ : S} (f : Π (x : T shape₁) (θ : T shape₂), T shape₃) (θ : T shape₂) : Prop

axiom is_bbtw_of_btw {shape₁ shape₂ shape₃ : S} (f : Π (x : T shape₁), T shape₃) (θ : T shape₂) :
  is_btw_exp₂ f → is_bounded_btw_exp₂_around (λ x θ₀, f x) θ

axiom is_bbtw_id {shape₁ shape₂ : S} (θ : T shape₂) : is_bounded_btw_exp₂_around (λ (x : T shape₁) (θ₀ : T shape₂), θ₀) θ

axiom is_bbtw_softplus {shape₁ shape₂ shape₃ : S} (f : T shape₁ → T shape₂ → T shape₃) (θ : T shape₂) :
  is_bounded_btw_exp₂_around f θ → is_bounded_btw_exp₂_around (λ x θ₀, softplus (f x θ₀)) θ

axiom is_bbtw_sum {shape₁ shape₂ shape₃ : S} (f : T shape₁ → T shape₂ → T shape₃) (θ : T shape₂) :
  is_bounded_btw_exp₂_around f θ → is_bounded_btw_exp₂_around (λ x θ₀, sum (f x θ₀)) θ

axiom is_bbtw_log_sigmoid {shape₁ shape₂ shape₃ : S} (f : T shape₁ → T shape₂ → T shape₃) (y : T shape₃) (θ : T shape₂) : y > 0 →
  is_bounded_btw_exp₂_around f θ → is_bounded_btw_exp₂_around (λ x θ₀, log (y + sigmoid (f x θ₀))) θ

axiom is_bbtw_log_1msigmoid {shape₁ shape₂ shape₃ : S} (f : T shape₁ → T shape₂ → T shape₃) (y : T shape₃) (θ : T shape₂) : y > 0 →
  is_bounded_btw_exp₂_around f θ → is_bounded_btw_exp₂_around (λ x θ₀, log (y + (1 - sigmoid (f x θ₀)))) θ

axiom is_bbtw_gemm {shape₁ shape₂ : S} {m n p : ℕ} (f : T shape₁ → T shape₂ → T [m, n]) (g : T shape₁ → T shape₂ → T [n, p]) (θ : T shape₂) :
  is_bounded_btw_exp₂_around f θ → is_bounded_btw_exp₂_around g θ → is_bounded_btw_exp₂_around (λ x θ₀, gemm (f x θ₀) (g x θ₀)) θ

axiom is_bbtw_neg {shape₁ shape₂ shape₃ : S} (f : T shape₁ → T shape₂ → T shape₃) (θ : T shape₂) :
  is_bounded_btw_exp₂_around f θ → is_bounded_btw_exp₂_around (λ x θ₀, - f x θ₀) θ

axiom is_bbtw_inv {shape₁ shape₂ shape₃ : S} (f : T shape₁ → T shape₂ → T shape₃) (θ : T shape₂) :
  is_bounded_btw_exp₂_around f θ → is_bounded_btw_exp₂_around (λ x θ₀, (f x θ₀)⁻¹) θ

axiom is_bbtw_add {shape₁ shape₂ shape₃ : S} (f g : T shape₁ → T shape₂ → T shape₃) (θ : T shape₂) :
  is_bounded_btw_exp₂_around f θ → is_bounded_btw_exp₂_around g θ → is_bounded_btw_exp₂_around (λ x θ₀, f x θ₀ + g x θ₀) θ

axiom is_bbtw_sub {shape₁ shape₂ shape₃ : S} (f g : T shape₁ → T shape₂ → T shape₃) (θ : T shape₂) :
  is_bounded_btw_exp₂_around f θ → is_bounded_btw_exp₂_around g θ → is_bounded_btw_exp₂_around (λ x θ₀, f x θ₀ - g x θ₀) θ

axiom is_bbtw_mul {shape₁ shape₂ shape₃ : S} (f g : T shape₁ → T shape₂ → T shape₃) (θ : T shape₂) :
  is_bounded_btw_exp₂_around f θ → is_bounded_btw_exp₂_around g θ → is_bounded_btw_exp₂_around (λ x θ₀, f x θ₀ * g x θ₀) θ

axiom is_bbtw_exp {shape₁ shape₂ shape₃ : S} (f : T shape₁ → T shape₂ → T shape₃) (θ : T shape₂) :
  is_sub_quadratic (λ x, f x θ) → (∀ x, is_sub_quadratic (f x)) → is_bounded_btw_exp₂_around (λ x θ₀, exp (f x θ₀)) θ

lemma is_bbtw_bernoulli_neglogpdf {shape₁ shape₂ shape₃ : S} (f : T shape₁ → T shape₂ → T shape₃) (θ : T shape₂) (p : T shape₃) :
  is_bounded_btw_exp₂_around f θ → is_bounded_btw_exp₂_around (λ x θ₀, bernoulli_neglogpdf (sigmoid (f x θ₀)) p) θ :=
begin
intro H,
dunfold bernoulli_neglogpdf,
apply is_bbtw_neg, apply is_bbtw_sum, apply is_bbtw_add,
apply is_bbtw_mul, apply is_bbtw_of_btw, apply is_btw_const, apply is_bbtw_log_sigmoid, exact eps_pos, exact H,
apply is_bbtw_mul, apply is_bbtw_of_btw, apply is_btw_const, apply is_bbtw_log_1msigmoid, exact eps_pos, exact H
end

-- misc
axiom integral_scale_shift_var {shape fshape : S} (f : T shape → T fshape) (α β : T shape) : ∫ (λ x, f (α * x + β)) = ∫ (λ x, prod α⁻¹ ⬝ f x)

@[simp]
lemma force_ok {shape : S} (x : T shape) : force x shape = x := by { dunfold force, simp }

end T

-- helper tactic
section tactic
open tactic list
meta def prove_preconditions_core : tactic unit :=
first (assumption :: map applyc [`certigrad.T.sqrt_pos, `certigrad.T.square_pos_of_pos, `certigrad.T.exp_pos,
                                 `certigrad.T.sigmoid_pos, `certigrad.T.sigmoid_lt1, `certigrad.T.lt1_alt, `certigrad.T.one_plus_pos,
                                 `certigrad.T.plus_one_pos, `certigrad.T.one_pos, `certigrad.T.neg_of_pos, `certigrad.T.const_pos_of_pos,
                                 `certigrad.T.mul_pos_of_pos_pos, `certigrad.T.add_pos_of_pos_pos,
                                 `certigrad.T.pi_pos, `certigrad.T.eps_pos,
                                 `certigrad.T.inv_pos, `certigrad.T.div_pos_pos, `certigrad.T.two_pos, `certigrad.T.two_pi_pos])

meta def prove_preconditions : tactic unit := repeat prove_preconditions_core
end tactic


end certigrad
