/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Tactics to prove specific models satisfy the preconditions of backprop_correct.

TODO(dhs): we are in the process of refactoring this tactic to use the simplifier
more aggressively and this file is currently in an inconsistent state.
-/
import .tfacts .graph .predicates .expected_value .reparam .kl .tactics .program

namespace certigrad
open T

/-
@[cgsimp] lemma pair_eq_of_eq {α β : Type*} (a₁ a₂ : α) (b₁ b₂ : β) : ((a₁, b₁) = (a₂, b₂)) = (a₁ = a₂ ∧ b₁ = b₂) := sorry
@[cgsimp] lemma id_str_eq_of_eq (x y : label) : (ID.str x = ID.str y) = (x = y) := sorry

-- TODO(dhs): tag the relevant existing simp lemmas as [cgsimp] instead of redefining them here.

@[cgsimp] lemma str_eq_of_char_eq (s₁ s₂ : string) : (s₁ = s₂) = (s₁^.to_list = s₂^.to_list) := sorry

attribute [cgsimp] ne string.to_list

example (s₁ s₂ : S) : (ID.str "ho", s₁) ≠ (ID.str "he", s₂) :=
begin
simp only with cgsimp,

end
-/
@[cgsimp] lemma simp_label (x : label): (lift_t x : ID) = (ID.str x : ID) := rfl
@[cgsimp] lemma label_of (x y : label) : (ID.str x = ID.str y) = (x = y) := sorry

@[cgsimp] lemma eq_of_self_eq {α : Type*} (x : α) : (x = x) = true := sorry
@[cgsimp] lemma prove_neq {α : Type*} (x y : α) : x ≠ y → x ≠ y := sorry

@[cgsimp] lemma true_of_in_nil {α : Type*} (P : Prop) (x : α) : (x ∈ @list.nil α → P) = true := sorry
@[cgsimp] lemma true_of_in_nil_alt {α : Type*} (P : α → Prop) (x : α) : (x ∈ @list.nil α → P x) = true := sorry
@[cgsimp] lemma and_true_left {P : Prop} : (true ∧ P) = P := sorry
@[cgsimp] lemma and_true_right {P : Prop} : (P ∧ true) = P := sorry
@[cgsimp] lemma true_of_imp_true {α : Type*} : (α → true) = true := sorry

@[cgsimp] lemma false_of_cons_eq_nil {α : Type*} {x : α} {xs : list α} : (list.cons x xs = list.nil) = false := sorry

@[cgsimp] lemma of_in_list_forall {α : Type*} (ys : list α) (P : α → Prop) (y : α) : (∀ x, x ∈ list.cons y ys → P x) = (P y ∧ (∀ x, x ∈ ys → P x)) := sorry

@[cgsimp] lemma of_in_list {α : Type*} (ys : list α) (x y : α) : (x ∈ list.cons y ys → false) = (x ≠ y ∧ (x ∈ ys → false)) := sorry

@[cgsimp] lemma simp_sqrt_pos {shape : S} : ∀ {x : T shape}, (0 < sqrt x) = (0 < x) := sorry
@[cgsimp] lemma simp_exp_pos {shape : S} : ∀ {x : T shape}, (0 < exp x) = true := sorry

@[cgsimp] lemma simp_integrable_pdf_add : Π {shape₁ shape₂ : S} (pdf : T shape₁ → ℝ) (f g : T shape₁ → T shape₂),
(is_integrable (λ (x : T shape₁), pdf x ⬝ (f x + g x))) = (is_integrable (λ (x : T shape₁), pdf x ⬝ f x) ∧ is_integrable (λ (x : T shape₁), pdf x ⬝ g x)) := sorry

-- TODO(dhs): prove continuous stuff with the simplifier
@[cgsimp] lemma simp_mvn_iso_bernoulli_neglogpdf_int {shape₁ shape₂ : S} (μ σ : T shape₁) (H_σ : 0 < σ) (p : T shape₁ → T shape₂)
                                                   /- (H_p_cont : ∀ x, is_continuous p x) -/ (H_p : ∀ x, 0 < p x ∧ p x < 1) (z : T shape₂) :
  is_integrable (λ (x : T shape₁), T.mvn_iso_pdf μ σ x ⬝ bernoulli_neglogpdf (p x) z) = true := sorry

@[cgsimp] lemma simp_mvn_iso_mvn_iso_empirical_kl_int {shape : S} (μ σ : T shape) (H_σ : 0 < σ) (μ' σ' : T shape) :
  is_integrable (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ mvn_iso_empirical_kl μ' σ' x) = true := sorry

@[cgsimp] lemma simp_mvn_iso_mvn_iso_kl_int {shape : S} (μ σ : T shape) (H_σ : 0 < σ) (μ' σ' : T shape) :
  is_integrable (λ (x : T shape), T.mvn_iso_pdf μ σ x ⬝ mvn_iso_kl μ' σ') = true := sorry

@[cgsimp] lemma simp_smul_zero (shape : S) (α : ℝ) : α ⬝ (0 : T shape) = (0 : T shape) := sorry
@[cgsimp] lemma simp_integrable_zero (shape₁ shape₂ : S) (y : T shape₂) : is_integrable (λ (x : T shape₁), y) = true := sorry

@[cgsimp] lemma simp_nneg_of_pos {shape : S} : ∀ {x : T shape}, 0 ≠ x = (0 < x ∨ 0 = x) := sorry

@[cgsimp] lemma simp_sigmoid_pos {shape : S} : ∀ {x : T shape}, (0 < sigmoid x) = true := sorry
@[cgsimp] lemma simp_sigmoid_lt1 {shape : S} : ∀ {x : T shape}, (sigmoid x < 1) = true := sorry

-- TODO(dhs): weird lemma
@[cgsimp] lemma simp_one_plus_pos {shape : S} : ∀ {x : T shape}, 0 < 1 + x = (0 < x ∨ - 1 < x) := sorry

attribute [cgsimp] hash_map.find_insert

attribute [cgsimp] dif_pos dif_neg dif_ctx_simp_congr

attribute [cgsimp] mvn_iso_mvn_iso_empirical_kl_int mvn_iso_bernoulli_neglogpdf_int

attribute [cgsimp] list.sumr list.map list.concat list.head list.tail

attribute [cgsimp] zero_add add_zero

attribute [cgsimp] dvec.head dvec.head2 dvec.head3

attribute [cgsimp] integrate_kl integrate_mvn_iso_kl integrate_kl_pre integrate_mvn_iso_kl_pre reparameterize

attribute [cgsimp] all_parents_in_env all_costs_scalars grads_exist_at pdfs_exist_at
                  is_gintegrable is_nabla_gintegrable is_gdifferentiable can_differentiate_under_integrals

attribute [cgsimp] graph.to_dist operator.to_dist sum_costs compute_grad_slow

attribute [cgsimp] E.E_bind E.E_ret

attribute [cgsimp] det.op.f det.special.f det.cwise1.f det.cwise2.f
                  det.function.neg det.function.exp det.function.log det.function.sqrt det.function.scale det.function.softplus det.function.sigmoid
                  det.function.add det.function.sub det.function.mul det.function.div
                  det.function.sum det.function.gemv det.function.gemm det.function.mul_add det.function.get_col_range
                  det.function.mvn_iso_kl det.function.mvn_iso_empirical_kl det.function.bernoulli_neglogpdf

attribute [cgsimp] rand.op.pdf rand.pdf.mvn_iso rand.pdf.mvn_iso_std
                  rand.op.pre rand.op.mvn_iso rand.op.mvn_iso_std rand.pre.mvn_iso rand.pre.mvn_iso_std

attribute [cgsimp] env.get_ks env.insert_all env.get_insert_same env.get_insert_diff
                  env.simp_has_key_insert_same env.simp_has_key_insert_diff env.simp_has_key_empty

attribute [cgsimp] program_to_graph program.program_to_graph_core
                  program.unary_to_cwise1 program.binary_to_cwise2 program.get_id
                  program.process_term program.empty_state program.process_rterm
                  program_to_graph._match_1
                  program.program_to_graph_core._match_1
                  program.program_to_graph_core._match_2
                  program.process_term._match_6
                  program.process_term._match_10
                  program.process_term._match_13
                  program.process_term._match_16
                  program.process_rterm._match_1
                  program.exp program.log program.sqrt program.softplus program.sigmoid

@[cgsimp] lemma lift_t_label_to_term (x : label) : (lift_t x : program.term) = (program.term.id x) := rfl

namespace tactic
open tactic

meta def gsimpt (tac : tactic unit) : tactic unit := do
  s ← join_user_simp_lemmas tt [`cgsimp],
  (at_target (λ e, do (a, new_e, pf) ← ext_simplify_core () {} s
                                                        (λ u, failed)
                                                        (λ a s r p e, failed)
                                                        (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core s tac r e,
                                                                         return ((), new_e, pr, tt))
                                                        `eq e,
                     return (new_e, pf)))

meta def cgsimpt (tac : tactic unit) : tactic unit := do
  s ← join_user_simp_lemmas tt [`cgsimp],
  repeat $ first [dsimp_core s, gsimpt tac, dec_triv]

meta def cgsimpn : ℕ → tactic unit
| 0 := cgsimpt skip
| (n+1) := cgsimpt (cgsimpn n)

meta def cgsimp : tactic unit := cgsimpn 5

end tactic
end certigrad
