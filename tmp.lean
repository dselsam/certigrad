import certigrad.prove_model_ok certigrad.aevb.util certigrad.mvn

namespace certigrad
namespace aevb

/-
f(t, x)
g(x) = ∫ ∇ (λ t, f(t x,))
g'(x) = ∫ ∇ (λ x, f(t, x))
  is_uniformly_integrable_around (λ θ₀ x, f x θ₀) θ →
  ∇ (λ θ₀, ∫ (λ x, f x θ₀)) θ = ∫ (λ x, ∇ (λ θ₀, f x θ₀) θ)

-------
x := θ
t := x
-------
g(θ) = ∫ (λ x, f θ x)

|f θ x| ≤ φ(x), ∀ θ
|f₁ θ x| ≤ ψ(x), ∀ θ

g'(θ) = ∫ (λ x, ∇ (λ θ₀, f θ₀ x) θ)
-/

--set_option pp.locals_full_names true
--set_option trace.simplify.rewrite_failure true
--set_option trace.simplify true

example (a : arch) (ws : weights a) (x_data : T [a.n_in, a.n_x]) (x : T [a.nz, a.bs]) :
T.is_cdifferentiable
  (λ (x_1 : ℝ),
     T.mvn_iso_pdf 0 1 x ⬝
       (T.mvn_iso_kl
            (T.gemm (ws.W_encode_μ)
               (T.softplus (T.gemm (ws.W_encode) (T.get_col_range (a.bs) x_data (T.round (ws.batch_start))))))
            (T.sqrt
               (T.exp
                  (T.gemm (ws.W_encode_logσ₂)
                     (T.softplus (T.gemm (ws.W_encode) (T.get_col_range (a.bs) x_data (T.round (ws.batch_start)))))))) +
          x_1))
  (T.bernoulli_neglogpdf
     (T.sigmoid
        (T.gemm (ws.W_decode_p)
           (T.softplus
              (T.gemm θ₀
                 (x *
                      T.sqrt
                        (T.exp
                           (T.gemm (ws.W_encode_logσ₂)
                              (T.softplus
                                 (T.gemm (ws.W_encode) (T.get_col_range (a.bs) x_data (T.round (ws.batch_start))))))) +
                    T.gemm (ws.W_encode_μ)
                      (T.softplus
                         (T.gemm (ws.W_encode) (T.get_col_range (a.bs) x_data (T.round (ws.batch_start))))))))))
     (T.get_col_range (a.bs) x_data (T.round (ws.batch_start)))) :=
begin
prove_differentiable,

end

set_option trace.simp_lemmas.rewrite.failure true
example (a : arch) (ws : weights a) (x_data : T [a.n_in, a.n_x]) :
    T.is_uniformly_integrable_around
           (λ (θ₀ : T ((ID.str label.W_decode, [a.nd, a.nz]).snd)) (x : T ((ID.str label.ε, [a.nz, a.bs]).snd)),
              ∇
                (λ (θ₁ : T ((ID.str label.W_decode, [a.nd, a.nz]).snd)),
                   T.mvn_iso_pdf 0 1 x ⬝
                     (T.mvn_iso_kl
                          (T.gemm (ws.W_encode_μ)
                             (T.softplus
                                (T.gemm (ws.W_encode) (T.get_col_range (a.bs) x_data (T.round (ws.batch_start))))))
                          (T.sqrt
                             (T.exp
                                (T.gemm (ws.W_encode_logσ₂)
                                   (T.softplus
                                      (T.gemm (ws.W_encode)
                                         (T.get_col_range (a.bs) x_data (T.round (ws.batch_start)))))))) +
                        T.bernoulli_neglogpdf
                          (T.sigmoid
                             (T.gemm (ws.W_decode_p)
                                (T.softplus
                                   (T.gemm θ₁
                                      (x *
                                           T.sqrt
                                             (T.exp
                                                (T.gemm (ws.W_encode_logσ₂)
                                                   (T.softplus
                                                      (T.gemm (ws.W_encode)
                                                         (T.get_col_range (a.bs) x_data
                                                            (T.round (ws.batch_start))))))) +
                                         T.gemm (ws.W_encode_μ)
                                           (T.softplus
                                              (T.gemm (ws.W_encode)
                                                 (T.get_col_range (a.bs) x_data (T.round (ws.batch_start))))))))))
                          (T.get_col_range (a.bs) x_data (T.round (ws.batch_start)))))
                θ₀)
           ws.W_decode :=
begin
--simp only [T.grad_scale_f],
T.simplify_grad,
trace "\n\nBOOOOOOO\n\n",
/-
simp only [T.grad_bernoulli_neglogpdf₁
                       (λ (θ₀ : ℝ),
                          T.mvn_iso_kl
                              (T.gemm (ws.W_encode_μ)
                                 (T.softplus
                                    (T.gemm (ws.W_encode)
                                       (T.get_col_range (a.bs) x_data
                                          (T.round (ws.batch_start))))))
                              (T.sqrt
                                 (T.exp
                                    (T.gemm (ws.W_encode_logσ₂)
                                       (T.softplus
                                          (T.gemm (ws.W_encode)
                                             (T.get_col_range (a.bs) x_data
                                                (T.round (ws.batch_start)))))))) + θ₀)]
-/

end
#exit

/-
axiom uintegrable_around_add {shape₁ shape₂ shape₃ : S} (pdf : T shape₁ → ℝ) (f g : T shape₁ → T shape₂ → T shape₃) (θ : T shape₂) :
   is_uniformly_integrable_around (λ θ₀ x, pdf x ⬝ f x θ₀) θ
→  is_uniformly_integrable_around (λ θ₀ x, pdf x ⬝ g x θ₀) θ
→  is_uniformly_integrable_around (λ θ₀ x, pdf x ⬝ (f x θ₀ + g x θ₀)) θ

axiom uintegrable_around_indep {shape₁ shape₂ shape₃ : S} (pdf : T shape₁ → ℝ) (f : T shape₁ → T shape₃) (θ : T shape₂) :
  is_integrable (λ x, pdf x ⬝ f x) →  is_uniformly_integrable_around (λ θ₀ x₀, pdf x₀ ⬝ f x₀) θ

axiom uintegrable_around_continuous {shape₁ shape₂ shape₃ : S} (pdf : T shape₁ → ℝ) (f : T shape₁ → T shape₂ → T shape₃) (θ : T shape₂) :
  is_integrable (λ x, pdf x ⬝ f x θ) →
  (∀ x, is_continuous (λ θ₀, pdf x ⬝ f x θ₀) θ) →
  is_uniformly_integrable_around (λ θ₀ x, pdf x ⬝ f x θ₀) θ
-/

end

end aevb
end certigrad
