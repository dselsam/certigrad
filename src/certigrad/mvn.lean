/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Properties of the multivariate isotropic Gaussian distribution.
-/
import .tfacts

namespace certigrad
namespace T

axiom is_integrable_mvn_of_sub_exp {shape₁ shape₂ : S} (μ σ : T shape₁) (f : T shape₁ → T shape₂) :
  is_btw_exp₂ f → is_integrable (λ x, mvn_iso_pdf μ σ x ⬝ f x)

axiom is_uintegrable_mvn_of_bounded_exp₂_around {shape₁ shape₂ shape₃ : S} (pdf : T shape₁ → ℝ) (f : T shape₁ → T shape₂ → T shape₃) (θ : T shape₂) :
  is_bounded_btw_exp₂_around f θ → is_uniformly_integrable_around (λ θ₀ x, pdf x ⬝ f x θ₀) θ

end T

section tactic
open tactic

meta def prove_is_mvn_integrable_core : tactic unit :=
first [
       applyc `certigrad.T.is_btw_id
     , applyc `certigrad.T.is_btw_const
     , applyc `certigrad.T.is_btw_sigmoid
     , applyc `certigrad.T.is_btw_softplus
     , applyc `certigrad.T.is_btw_sum
     , applyc `certigrad.T.is_btw_log_sigmoid
     , applyc `certigrad.T.is_btw_log_1msigmoid
     , applyc `certigrad.T.is_btw_gemm
     , applyc `certigrad.T.is_btw_transpose
     , applyc `certigrad.T.is_btw_neg
     , applyc `certigrad.T.is_btw_inv
     , applyc `certigrad.T.is_btw_add
     , applyc `certigrad.T.is_btw_mul
     , applyc `certigrad.T.is_btw_sub
     , applyc `certigrad.T.is_btw_div
     , applyc `certigrad.T.is_btw_exp

     , applyc `certigrad.T.is_linear_id
     , applyc `certigrad.T.is_linear_const
     , applyc `certigrad.T.is_linear_gemm
     , applyc `certigrad.T.is_linear_transpose
     , applyc `certigrad.T.is_linear_neg
     , applyc `certigrad.T.is_linear_inv
     , applyc `certigrad.T.is_linear_add
     , applyc `certigrad.T.is_linear_mul
     , applyc `certigrad.T.is_linear_sub
     , applyc `certigrad.T.is_linear_div
]

meta def prove_is_mvn_integrable : tactic unit :=
do applyc `certigrad.T.is_integrable_mvn_of_sub_exp,
   repeat prove_is_mvn_integrable_core

meta def prove_is_mvn_uintegrable_core : tactic unit :=
first [applyc `certigrad.T.is_bbtw_id_of_btw
     , applyc `certigrad.T.is_bbtw_bernoulli_neglogpdf
     , applyc `certigrad.T.is_bbtw_softplus
     , applyc `certigrad.T.is_bbtw_sum
     , applyc `certigrad.T.is_bbtw_log_sigmoid
     , applyc `certigrad.T.is_bbtw_log_1msigmoid
     , applyc `certigrad.T.is_bbtw_gemm
     , applyc `certigrad.T.is_bbtw_gemm₁
     , applyc `certigrad.T.is_bbtw_neg
     , applyc `certigrad.T.is_bbtw_mul
     , applyc `certigrad.T.is_bbtw_add
]

meta def prove_is_mvn_uintegrable : tactic unit :=
do applyc `certigrad.T.is_uintegrable_mvn_of_bounded_exp₂_around,
   repeat (prove_is_mvn_uintegrable_core <|> prove_is_mvn_integrable_core)

end tactic

namespace T
axiom mvn_iso_const_int {shape oshape : S} (μ σ : T shape) : σ > 0 → ∀ (y : T oshape), is_integrable (λ (x : T shape), mvn_iso_pdf μ σ x ⬝ y)
axiom mvn_iso_moment₁_int {shape : S} (μ σ : T shape) : σ > 0 → is_integrable (λ (x : T shape), mvn_iso_pdf μ σ x ⬝ x)
axiom mvn_iso_moment₂_int {shape : S} (μ σ : T shape) : σ > 0 → is_integrable (λ (x : T shape), mvn_iso_pdf μ σ x ⬝ square x)
axiom mvn_iso_cmoment₂_int {shape : S} (μ σ : T shape) (H_σ : σ > 0) : is_integrable (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ square (x - μ))

axiom mvn_iso_logpdf_int {shape : S} (μ μ' σ σ' : T shape) (H_σ : σ > 0) (H_σ' : σ' > 0) : is_integrable (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ mvn_iso_logpdf μ' σ' x)

-- TODO(dhs): prove in terms of primitives (possibly for concrete p)
axiom mvn_iso_bernoulli_neglogpdf_int {shape₁ shape₂ : S} (μ σ : T shape₁) (H_σ : σ > 0) (p : T shape₁ → T shape₂)
                                      (H_p_cont : ∀ x, is_continuous p x) (H_p : ∀ x, p x > 0 ∧ p x < 1) (z : T shape₂) :
  is_integrable (λ (x : T shape₁), T.mvn_iso_pdf μ σ x ⬝ bernoulli_neglogpdf (p x) z)

axiom mvn_iso_mvn_iso_empirical_kl_int {shape : S} (μ σ : T shape) (H_σ : σ > 0) (μ' σ' : T shape) :
  is_integrable (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ mvn_iso_empirical_kl μ' σ' x)

axiom mvn_iso_mvn_iso_kl_int {shape : S} (μ σ : T shape) (H_σ : σ > 0) (μ' σ' : T shape) :
  is_integrable (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ mvn_iso_kl μ' σ')

-- mvn_iso is a distribution (provable from first principles)
axiom mvn_iso_pdf_pos {shape : S} (μ σ : T shape) : σ > 0 → ∀ (x : T shape), mvn_iso_pdf μ σ x > 0
axiom mvn_iso_pdf_int1 {shape : S} (μ σ : T shape) : σ > 0 → ∫ (λ (x : T shape), mvn_iso_pdf μ σ x) = 1

lemma mvn_iso_expected {shape oshape : S} (μ σ : T shape) : σ > 0 → ∀ (y : T oshape), ∫ (λ (x : T shape), mvn_iso_pdf μ σ x ⬝ y) = y :=
by { intros H_σ y, rw [integral_fscale, (mvn_iso_pdf_int1 _ _ H_σ), one_smul] }

-- moments (provable from first principles)
axiom mvn_iso_moment₁ {shape : S} (μ σ : T shape) (H_σ : σ > 0) : ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ x) = μ
axiom mvn_iso_moment₂ {shape : S} (μ σ : T shape) (H_σ : σ > 0) : ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ square x) = square μ + square σ

-- central moments (provable in terms of moments)
lemma mvn_iso_cmoment₁ {shape : S} (μ σ : T shape) (H_σ : σ > 0) : ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ (x - μ)) = 0 :=
have H_int_x : is_integrable (λ x, mvn_iso_pdf μ σ x ⬝ x), from mvn_iso_moment₁_int μ σ H_σ,
have H_int_μ : is_integrable (λ x, - (mvn_iso_pdf μ σ x ⬝ μ)), from iff.mp (is_integrable_neg _) (mvn_iso_const_int μ σ H_σ μ),
calc  ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ (x - μ))
    = ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ x + - (T.mvn_iso_pdf μ σ x ⬝ μ)) : begin simp [smul_addr, smul_neg], end
... = ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ x) - ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ μ)
        : begin simp [integral_add, H_int_x, H_int_μ, integral_neg] end
... = μ - μ : by { rw [mvn_iso_expected _ _ H_σ, mvn_iso_moment₁ _ _ H_σ],  }
... = 0 : by simp

-- Exercise for the reader: prove
axiom mvn_iso_cmoment₂ {shape : S} (μ σ : T shape) (H_σ : σ > 0) : ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ square (x - μ)) = square σ

-- central scaled moments (provable in terms of central moments)
lemma mvn_iso_csmoment₁ {shape : S} (μ σ : T shape) (H_σ : σ > 0) : ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ ((x - μ) / σ)) = 0 :=
have H_int_xσ : is_integrable (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ (x / σ)),
  by { simp [smul_div], exact iff.mp (is_integrable_div _ _ H_σ) (mvn_iso_moment₁_int _ _ H_σ) },

have H_int_μσ : is_integrable (λ (x : T shape), -(T.mvn_iso_pdf μ σ x ⬝ (μ / σ))),
 by { apply iff.mp (is_integrable_neg _), simp [smul_div], exact iff.mp (is_integrable_div _ _ H_σ) (mvn_iso_const_int _ _ H_σ _) },

calc  ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ ((x - μ) / σ))
    = ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ (x / σ) - (T.mvn_iso_pdf μ σ x ⬝ (μ / σ)))
        : by simp [T.div_add_div_same_symm, smul_addr, sum_add, neg_div, smul_neg, integral_neg]
... = ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ (x / σ)) - ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ (μ / σ))
        : begin simp [integral_add, H_int_xσ, H_int_μσ, integral_neg] end
... = ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ x) / σ - ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ (μ / σ))
        : by simp [smul_div, integral_div]
... = μ / σ - μ / σ : by rw [mvn_iso_moment₁ _ _ H_σ, mvn_iso_expected _ _ H_σ]
... = 0 : by simp

-- Exercise for the reader: prove
axiom mvn_iso_csmoment₂ {shape : S} (μ σ : T shape) (H_σ : σ > 0) : ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ square ((x - μ) / σ)) = (1 : T shape)

lemma mvn_iso_logpdf_correct {shape : S} (μ σ x : T shape) : log (mvn_iso_pdf μ σ x) = mvn_iso_logpdf μ σ x :=
calc  log (mvn_iso_pdf μ σ x)
    = log (prod ((sqrt ((2 * pi shape) * square σ))⁻¹ * exp ((- 2⁻¹) * (square $ (x - μ) / σ)))) : rfl
... = sum (log ((sqrt ((2 * pi shape) * square σ))⁻¹) + ((- 2⁻¹) * (square $ (x - μ) / σ))) : by simp only [log_prod, log_mul, log_exp]
... = sum ((- 2⁻¹) * log ((2 * pi shape) * square σ) + ((- 2⁻¹) * (square $ (x - μ) / σ))) : by simp [log_inv, log_sqrt]
... = sum ((- 2⁻¹) * (log (2 * pi shape) + log (square σ)) + (- 2⁻¹) * (square $ (x - μ) / σ)) : by simp only [log_mul]
... = sum ((- 2⁻¹) * (log (2 * pi shape) + log (square σ) + (square $ (x - μ) / σ))) : by simp only [left_distrib]
... = sum ((- (2 : ℝ)⁻¹) ⬝ (log (2 * pi shape) + log (square σ) + (square $ (x - μ) / σ))) : by simp only [smul.def, const_neg, const_inv, const_bit0, const_one]
... = (- 2⁻¹) * sum (square ((x - μ) / σ) + log (2 * pi shape) + log (square σ)) : by simp [sum_smul]
... = mvn_iso_logpdf μ σ x : rfl

lemma mvn_int_const {shape : S} (μ σ : T shape) (H_σ : σ > 0) (y : ℝ) :
  ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ y) = y :=
by { rw [integral_fscale, (mvn_iso_pdf_int1 _ _ H_σ), one_smul] }

lemma mvn_integral₁ {shape : S} (μ σ : T shape) (H_σ : σ > 0) :
∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ T.mvn_iso_logpdf 0 1 x)
=
(- 2⁻¹) * sum (square μ + square σ) + (- 2⁻¹) * sum (log (2 * pi shape)) :=
have H_sq_x_int : is_integrable (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ square x), from mvn_iso_moment₂_int _ _ H_σ,
have H_log_pi_int : is_integrable (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ log (2 * pi shape)), from mvn_iso_const_int _ _ H_σ _,
have H_sum_int : is_integrable (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ (square x + log (2 * pi shape))),
  begin simp only [smul_addr], exact iff.mp (is_integrable_add _ _) (and.intro H_sq_x_int H_log_pi_int) end,
calc  ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ ((- 2⁻¹) * sum (square ((x - 0) / 1) + log (2 * pi shape) + log (square 1))))
    = ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ ((- 2⁻¹) * sum (square x + log (2 * pi shape)))) : by simp [log_one, square, T.div_one]
... = ∫ (λ (x : T shape), (- (2 : ℝ)⁻¹) ⬝ (T.mvn_iso_pdf μ σ x ⬝ sum (square x + log (2 * pi shape)))) : by simp only [smul_mul_scalar_right]
... = (- 2⁻¹) * ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ sum (square x + log (2 * pi shape))) : by { simp only [integral_scale], simp [smul.def] }
... = (- 2⁻¹) * sum (∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ (square x + log (2 * pi shape)))) : by { simp only [integral_sum, H_sum_int, smul_sum] }
... = (- 2⁻¹) * sum (∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ square x + T.mvn_iso_pdf μ σ x ⬝ log (2 * pi shape))) : by { simp only [smul_addr] }
... = (- 2⁻¹) * sum (∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ square x) + ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ log (2 * pi shape)))
       : by { simp only [integral_add, H_sq_x_int, H_log_pi_int] }
... = (- 2⁻¹) * (sum (square μ + square σ) + sum (log (2 * pi shape))) : by rw [mvn_iso_moment₂ _ _ H_σ, mvn_iso_expected _ _ H_σ, sum_add]
... = (- 2⁻¹) * sum (square μ + square σ) + (- 2⁻¹) * sum (log (2 * pi shape)) : by rw left_distrib

lemma mvn_integral₂ {shape : S} (μ σ : T shape) (H_σ : σ > 0) :
∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ T.mvn_iso_logpdf μ σ x)
=
(- 2⁻¹) * sum (1 : T shape) + (- 2⁻¹) * sum (log (2 * pi shape)) + (- 2⁻¹) * sum (log (square σ)) :=
have H_int₁ : is_integrable (λ (x : T shape), mvn_iso_pdf μ σ x ⬝ (-2⁻¹ * sum (square ((x - μ) / σ)))),
begin
simp only [smul_mul_scalar_right, integral_scale],
apply iff.mp (is_integrable_scale _ _),
simp only [smul_sum],
apply iff.mp (is_integrable_sum _),
simp only [square_div, smul_div],
apply iff.mp (is_integrable_div _ _ (square_pos_of_pos H_σ)),
exact mvn_iso_cmoment₂_int _ _ H_σ,
end,

have H_int₂ : is_integrable (λ (x : T shape), mvn_iso_pdf μ σ x ⬝ (-2⁻¹ * sum (log (2 * pi shape)))),
begin
simp only [smul_mul_scalar_right, integral_scale],
apply iff.mp (is_integrable_scale _ _),
simp only [smul_sum],
apply iff.mp (is_integrable_sum _),
exact mvn_iso_const_int _ _ H_σ _
end,

have H_int₁₂ : is_integrable (λ (x : T shape), mvn_iso_pdf μ σ x ⬝ (-2⁻¹ * sum (square ((x - μ) / σ))) + mvn_iso_pdf μ σ x ⬝ (-2⁻¹ * sum (log (2 * pi shape)))),
from iff.mp (is_integrable_add _ _) (and.intro H_int₁ H_int₂),

have H_int₃ : is_integrable (λ (x : T shape), mvn_iso_pdf μ σ x ⬝ (-2⁻¹ * sum (log (square σ)))),
begin
simp only [smul_mul_scalar_right, integral_scale],
apply iff.mp (is_integrable_scale _ _),
simp only [smul_sum],
apply iff.mp (is_integrable_sum _),
exact mvn_iso_const_int _ _ H_σ _
end,

have H_int₄ : is_integrable (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ square ((x - μ) / σ)),
begin
simp only [square_div, smul_div],
apply iff.mp (is_integrable_div _ _ (square_pos_of_pos H_σ)),
exact mvn_iso_cmoment₂_int _ _ H_σ,
end,

have H₁ : ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ ((- 2⁻¹) * sum (square ((x - μ) / σ)))) = (- 2⁻¹) * sum (1 : T shape), from
calc  ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ ((- 2⁻¹) * sum (square ((x - μ) / σ))))
    = ∫ (λ (x : T shape), (- (2 : ℝ)⁻¹) ⬝ (T.mvn_iso_pdf μ σ x ⬝ sum (square ((x - μ) / σ)))) : by simp only [smul_mul_scalar_right]
... = (- 2⁻¹) * ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ sum (square ((x - μ) / σ))) : by { simp only [integral_scale], simp [smul.def] }
... = (- 2⁻¹) * sum (∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ square ((x - μ) / σ))) : by simp only [smul_sum, integral_sum, H_int₄]
... = (- 2⁻¹) * sum (1 : T shape) : by rw (mvn_iso_csmoment₂ _ _ H_σ),

have H₂ : ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ ((- 2⁻¹) * sum (log (2 * pi shape)))) = (- 2⁻¹) * sum (log (2 * pi shape)), by rw (mvn_int_const μ _ H_σ),

have H₃ : ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ ((- 2⁻¹) * sum (log (square σ)))) = (- 2⁻¹) * sum (log (square σ)), by rw mvn_int_const μ _ H_σ,
begin
dunfold mvn_iso_logpdf,
simp only [sum_add, left_distrib, smul_addr, integral_add, H₁, H₂, H₃, H_int₁₂, H_int₁, H_int₂, H_int₃],
end

lemma mvn_iso_kl_identity {shape : S} (μ σ : T shape) (H_σ : σ > 0) :
∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ T.mvn_iso_empirical_kl μ σ x)
=
T.mvn_iso_kl μ σ :=
have H_logpdf_int : is_integrable (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ mvn_iso_logpdf μ σ x),
from mvn_iso_logpdf_int μ μ σ σ H_σ H_σ,

have H_std_logpdf_int : is_integrable (λ (x : T shape), - (T.mvn_iso_pdf μ σ x ⬝ mvn_iso_logpdf 0 1 x)),
from iff.mp (is_integrable_neg _) (mvn_iso_logpdf_int μ 0 σ 1 H_σ one_pos),

calc  ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ T.mvn_iso_empirical_kl μ σ x)
    = ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ (mvn_iso_logpdf μ σ x - mvn_iso_logpdf 0 1 x)) : rfl
... = ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ mvn_iso_logpdf μ σ x + - (T.mvn_iso_pdf μ σ x ⬝ mvn_iso_logpdf 0 1 x)) : by simp [smul_addr, smul_neg]
... = ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ mvn_iso_logpdf μ σ x) - ∫ (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ mvn_iso_logpdf 0 1 x)
      : by simp [integral_add, H_logpdf_int, H_std_logpdf_int, integral_neg]
... = ((- 2⁻¹) * sum (1 : T shape) + (- 2⁻¹) * sum (log (2 * pi shape)) + (- 2⁻¹) * sum (log (square σ))) - ((- 2⁻¹) * sum (square μ + square σ) + (- 2⁻¹) * sum (log (2 * pi shape))) : by rw [mvn_integral₁ μ σ H_σ, mvn_integral₂ μ σ H_σ]
... = (- 2⁻¹) * sum ((1 : T shape) + log (2 * pi shape) + log (square σ) - square μ - square σ - log (2 * pi shape)) : by simp [sum_add, left_distrib, sum_neg]
... = (- 2⁻¹) * sum ((1 : T shape) + log (square σ) - square μ - square σ + (log (2 * pi shape) - log (2 * pi shape))) : by simp
... = (- 2⁻¹) * sum ((1 : T shape) + log (square σ) - square μ - square σ) : by simp
... = T.mvn_iso_kl μ σ : rfl

end T
end certigrad
