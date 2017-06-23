/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Tactics to prove specific models satisfy the preconditions of backprop_correct.

TODO(dhs): we are in the process of refactoring this tactic to use the simplifier
more aggressively and this file is currently in an inconsistent state.
-/
import data.list.set .tfacts .graph .predicates .expected_value .reparam .kl .tactics .program .pre .mvn .tactics

namespace certigrad
open T tactic

def pextt {P : Prop} : P → (P = true) := λ Hp, propext (iff_true_intro Hp)
def pextf {P : Prop} : ¬ P → (P = false) := λ Hnp, propext (iff.intro (λ Hp, Hnp Hp) (λ Hf, false.rec _ Hf))

lemma mem_of_ne_mem_cons {α : Type*} {xs : list α} {x y : α} : x ∈ y :: xs → x ≠ y → x ∈ xs :=
begin
intros H_in H_neq,
dunfold has_mem.mem list.mem at H_in,
cases H_in with H_eq H_in,
exfalso, exact H_neq H_eq, exact H_in
end

@[cgsimp] lemma true_of_not_false : (¬ false) = true :=
begin apply propext, split, intro H, exact trivial, intros Ht Hf, exact Hf end

@[cgsimp] lemma label_of (x y : label) : (ID.str x = ID.str y) = (x = y) :=
begin apply propext, split, intro H, injection H, intro H, rw H end

@[cgsimp] lemma eq_of_self_eq {α : Type*} (x : α) : (x = x) = true := propext (eq_self_iff_true _)

@[cgsimp] lemma and_true_left {P : Prop} : (true ∧ P) = P := propext (true_and _)
@[cgsimp] lemma and_true_right {P : Prop} : (P ∧ true) = P := propext (and_true _)
@[cgsimp] lemma true_of_imp_true {α : Sort*} : (α → true) = true := propext (iff.intro (λ H, trivial) (λ H x, trivial))

@[cgsimp] lemma simp_nodup_nil {α : Type*} : @list.nodup α [] = true := pextt list.nodup_nil

@[cgsimp] lemma simp_nodup_singleton {α : Type*} (a : α) : list.nodup [a] = true := pextt (list.nodup_singleton _)
@[cgsimp] lemma simp_nodup_cons {α : Type*} {a : α} {l : list α} (H : a ∉ l) : list.nodup (a::l) = list.nodup l :=
begin apply propext, split, intro H', cases H' with H1 H2 H3 H4, exact H4, apply list.nodup_cons, exact H end

@[cgsimp] lemma false_imp {P : Prop} : (false → P) = true :=
begin apply propext, split, intro H, exact trivial, intros Ht Hf, exfalso, exact Hf end
@[cgsimp] lemma true_imp {P : Prop} : (true → P) = P :=
begin apply propext, split, intro H, exact H trivial, intros H Ht, exact H end

@[cgsimp] lemma simp_mem_nil {α : Type*} (x : α) : (x ∈ @list.nil α) = false :=
begin apply pextf, apply list.not_mem_nil end

@[cgsimp] lemma simp_mem_cons_neq {α : Type*} (x y : α) (xs : list α) : x ≠ y → (x ∈ y :: xs) = (x ∈ xs) :=
begin intro H_neq, apply propext, split, intro H_in, exact mem_of_ne_mem_cons H_in H_neq, intro H_in, exact or.inr H_in end

@[cgsimp] lemma simp_mem_cons_eq {α : Type*} (x y : α) (xs : list α) : x = y → (x ∈ y :: xs) = true :=
begin intro H_eq, apply pextt, dunfold has_mem.mem list.mem, left, exact H_eq end

@[cgsimp] lemma simp_nmem_nil {α : Type*} (x : α) : (x ∉ @list.nil α) = true :=
begin apply pextt, apply list.not_mem_nil end

@[cgsimp] lemma simp_nmem_cons_eq {α : Type*} (x y : α) (xs : list α) : x ≠ y → (x ∉ y :: xs) = (x ∉ xs) :=
begin intro H_neq, apply propext, split, intros H_nin H_in, exact H_nin (or.inr H_in),
intros H_nin H_in, exact H_nin (mem_of_ne_mem_cons H_in H_neq)
end

@[cgsimp] lemma simp_nmem_cons_neq {α : Type*} (x y : α) (xs : list α) : x = y → (x ∉ y :: xs) = false :=
begin intro H_eq, apply pextf, intro H, exact H (or.inl H_eq) end

@[cgsimp] lemma false_of_cons_eq_nil {α : Type*} {x : α} {xs : list α} : (list.cons x xs = list.nil) = false :=
begin apply pextf, intro H, injection H end

@[cgsimp] lemma simp_at_idx_nil {α : Type*} [inhabited α] (x : α) (idx : ℕ) : list.at_idx list.nil idx x = false :=
begin
apply pextf,
intro H,
dunfold list.at_idx at H,
cases H with H1 H2,
exact (nat.not_lt_zero idx) H1
end

@[cgsimp] lemma simp_at_idx_0 {α : Type*} [inhabited α] {x : α} {xs : list α} : list.at_idx (x::xs) 0 x = true :=
begin apply pextt, apply list.at_idx_0 end

@[cgsimp] lemma simp_at_idx_cons {α : Type*} [inhabited α] {x : α} {xs : list α} {y : α} {idx : ℕ} :
  list.at_idx (x::xs) (idx+1) y = list.at_idx xs idx y :=
begin
apply propext,
split,
apply list.at_idx_of_cons,
apply list.at_idx_cons
end

@[cgsimp] lemma of_in_list_forall_cons {α : Type*} (ys : list α) (P : α → Prop) (y : α) : (∀ x, x ∈ list.cons y ys → P x) = (P y ∧ (∀ x, x ∈ ys → P x)) :=
begin
apply propext,
split,
intro H,
{ split, exact H y list.mem_of_cons_same, intros x H_in, exact H x (or.inr H_in) },
{
intro H, cases H with HPy H, intros x H_in,
cases classical.em (x = y) with H_eq H_neq,
rw H_eq, exact HPy,
exact H x (mem_of_ne_mem_cons H_in H_neq)
}
end

@[cgsimp] lemma of_in_list_forall_nil {α : Type*} (P : α → Prop) (y : α) : (∀ (x : α), x ∈  @list.nil α → P x) = true :=
begin
apply pextt,
intros x H_in_nil,
exfalso,
exact (list.not_mem_nil _) H_in_nil
end

@[cgsimp] lemma of_in_list_cons_neq {α : Type*} {P : Prop} (ys : list α) (x y : α) : x ≠ y → (x ∈ list.cons y ys → P) = (x ∈ ys → P) :=
begin
intro H_neq,
apply propext,
split,
intro H,
intro H_in,
apply H,
exact or.inr H_in,
intro H,
intro H_in,
apply H,
exact mem_of_ne_mem_cons H_in H_neq
end

@[cgsimp] lemma of_in_list_cons_eq {α : Type*} {P : Prop} (ys : list α) (x y : α) : x = y → (x ∈ list.cons y ys → P) = P :=
begin
intro H_eq,
apply propext,
split,
intro H_in,
exact H_in (or.inl H_eq),
intros HP H_in,
exact HP
end

@[cgsimp] lemma simp_sublist_cons {α : Type*} (xs : list α) (x : α) : (xs <+ x :: xs) = true :=
begin
apply pextt,
apply list.sublist_cons
end

@[cgsimp] lemma simp_sqrt_pos {shape : S} {x : T shape}: (0 < sqrt x) = (0 < x) :=
begin apply propext, split, apply pos_of_sqrt_pos, apply sqrt_pos end

@[cgsimp] lemma simp_exp_pos {shape : S} {x : T shape} : (0 < exp x) = true :=
begin apply pextt, apply exp_pos end

@[cgsimp] lemma simp_integrable_const (shape₁ shape₂ : S) (y : T shape₂) : is_integrable (λ (x : T shape₁), y) = true :=
begin apply pextt, apply is_integrable_const end

@[cgsimp] lemma simp_nneg_of_pos {shape : S} {x : T shape} : x ≠ 0 = (0 < x ∨ x < 0) :=
begin apply propext, apply nz_iff end

@[cgsimp] lemma simp_one_pos {shape : S} : (0 < (1 : T shape)) = true := pextt one_pos

@[cgsimp] lemma simp_sigmoid_pos {shape : S} {x : T shape} : (0 < sigmoid x) = true := pextt sigmoid_pos
@[cgsimp] lemma simp_sigmoid_lt1 {shape : S} {x : T shape} : (sigmoid x < 1) = true := pextt sigmoid_lt1

-- TODO(dhs): weird lemma
@[cgsimp] lemma simp_one_plus_pos {shape : S} {x : T shape} : 0 < 1 + x = (0 < x ∨ - 1 < x) :=
begin
apply propext,
split,
intro H,
right, exact iff.mp one_plus_pos_iff H,
intro H,
cases H with H H,
apply one_plus_pos,
exact H,
exact iff.mpr one_plus_pos_iff H
end

@[cgsimp] lemma simp_has_key_insert_same (ref : reference) {x : T ref.2} (m : env) :
  env.has_key ref (env.insert ref x m) = true := pextt (by apply env.has_key_insert_same)

@[cgsimp] lemma simp_has_key_insert_diff (ref₁ ref₂ : reference) {x : T ref₂.2} (m : env) :
  ref₁ ≠ ref₂ → env.has_key ref₁ (env.insert ref₂ x m) = env.has_key ref₁ m :=
begin
intro H_neq,
apply propext,
split,
apply env.has_key_insert_diff,
exact H_neq,
apply env.has_key_insert
end

@[cgsimp] lemma simp_has_key_empty (ref : reference) : env.has_key ref env.mk = false :=
begin apply pextf, apply env.not_has_key_empty end

attribute [cgsimp] T.smul_zero T.one_smul

attribute [cgsimp] if_pos if_neg if_true if_false

attribute [cgsimp] dif_pos dif_neg dif_ctx_simp_congr

attribute [cgsimp] mvn_iso_mvn_iso_empirical_kl_int mvn_iso_bernoulli_neglogpdf_int

attribute [cgsimp] force_ok

attribute [cgsimp] list.sumr list.map list.concat list.head list.tail list.riota list.filter list.length list.dnth
                   list.sublist.refl list.nil_subset list.sublist_cons list.cons_append list.append_nil list.nil_append

attribute [cgsimp] hash_map.find_insert_eq hash_map.find_insert_ne

attribute [cgsimp] zero_add add_zero

attribute [cgsimp] dvec.head dvec.head2 dvec.head3

attribute [cgsimp] integrate_kl integrate_mvn_iso_kl integrate_kl_pre integrate_mvn_iso_kl_pre reparameterize
attribute [cgsimp] reparam reparameterize reparameterize_pre

attribute [cgsimp] all_parents_in_env all_costs_scalars grads_exist_at pdfs_exist_at all_pre_satisfied uniq_ids
                   is_gintegrable is_nabla_gintegrable is_gdifferentiable can_differentiate_under_integrals

attribute [cgsimp] graph.to_dist operator.to_dist sum_costs compute_grad_slow

attribute [cgsimp] E.E_bind E.E_ret

attribute [cgsimp] det.op.f det.special.f det.cwise1.f det.cwise2.f
                  det.function.neg det.function.exp det.function.log det.function.sqrt det.function.scale det.function.softplus det.function.sigmoid
                  det.function.add det.function.sub det.function.mul det.function.div
                  det.function.sum det.function.gemv det.function.gemm det.function.mul_add det.function.get_col_range
                  det.function.mvn_iso_kl det.function.mvn_iso_empirical_kl det.function.bernoulli_neglogpdf

attribute [cgsimp] det.op.pre det.special.pre det.cwise1.pre det.cwise2.pre
                   det.preconditions.predicates.top det.preconditions.predicates.bot det.preconditions.predicates.pos
                   det.preconditions.neg det.preconditions.exp det.preconditions.log det.preconditions.sqrt det.preconditions.scale
                   det.preconditions.softplus det.preconditions.sigmoid
                   det.preconditions.add det.preconditions.sub det.preconditions.mul det.preconditions.div
                   det.preconditions.sum det.preconditions.gemv det.preconditions.gemm
                   det.preconditions.replicate_col det.preconditions.mul_add det.preconditions.mvn_iso_kl det.preconditions.mvn_iso_empirical_kl
                   det.preconditions.bernoulli_neglogpdf

attribute [cgsimp] det.op.pb det.cwise1.pb det.cwise2.pb det.special.pb
                   det.pullback.dummy
                   det.pullback.neg det.pullback.exp det.pullback.log det.pullback.sqrt det.pullback.scale
                   det.pullback.softplus det.pullback.sigmoid det.pullback.add det.pullback.sub det.pullback.mul det.pullback.div
                   det.pullback.sum det.pullback.gemm det.pullback.replicate_col det.pullback.mul_add
                   det.pullback.mvn_iso_kl det.pullback.mvn_iso_empirical_kl det.pullback.bernoulli_neglogpdf

attribute [cgsimp] rand.op.pdf rand.pdf.mvn_iso rand.pdf.mvn_iso_std
                   rand.op.pre rand.op.mvn_iso rand.op.mvn_iso_std rand.pre.mvn_iso rand.pre.mvn_iso_std

attribute [cgsimp] env.get_ks env.insert_all env.get_insert_same env.get_insert_diff

attribute [cgsimp] list.insertion_sort list.ordered_insert

attribute [cgsimp] program_to_graph program.program_to_graph_core
                  program.unary_to_cwise1 program.binary_to_cwise2 program.get_id
                  program.process_term program.empty_state program.process_rterm
                  program_to_graph._match_1
                  program.program_to_graph_core._match_1
                  program.program_to_graph_core._match_2
                  program.process_rterm._match_1
                  program.process_term._match_6
                  program.process_term._match_10
                  program.process_term._match_13
                  program.process_term._match_16
                  program.process_term._match_17
                  program.exp program.log program.sqrt program.softplus program.sigmoid

@[cgsimp] lemma lift_t_label_to_term (x : label) : (lift_t x : program.term) = (program.term.id x) := rfl
@[cgsimp] lemma lift_t_tensor_to_term (shape : S) (x : T shape) : (lift_t x : program.term) = (program.term.const x) := rfl

namespace tactic
open tactic

meta def dcgsimp : tactic unit := do
  s ← join_user_simp_lemmas tt [`cgsimp],
  dsimp_core s

meta def gsimpt (tac : tactic unit) : tactic unit := do
  s ← join_user_simp_lemmas tt [`cgsimp],
  tgt ← target,
  (a, new_tgt, pf) ← ext_simplify_core () {} s
                                     (λ u, failed)
                                     (λ a s r p e, failed)
                                     (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core reducible s tac r e,
                                                      return ((), new_e, pr, tt))
                                     `eq tgt,
  replace_target new_tgt pf

meta def cgsimpt (tac : tactic unit) : tactic unit := do
  s ← join_user_simp_lemmas tt [`cgsimp],
  repeat $ first [gsimpt tac, prove_refs_neq, prove_ids_neq, triv]

meta def cgsimpn : ℕ → tactic unit
| 0 := cgsimpt skip
| (n+1) := cgsimpt (cgsimpn n)

meta def cgsimp : tactic unit := cgsimpn 50

meta def forall_idxs (tac_base tac_step : tactic unit) : expr → tactic unit
| idx :=
tac_base <|>
(do cases idx [`_idx],
    solve1 tac_step,
    get_local `_idx >>= forall_idxs)

meta def prove_model_base : tactic unit :=
do exfalso,
   H_at_idx ← get_local `H_at_idx,
to_expr ```(list.at_idx_over %%H_at_idx dec_trivial) >>= exact

meta def prove_model_step : tactic unit :=
do H_at_idx ← get_local `H_at_idx,
   mk_app `and.right [H_at_idx] >>= note `H_tgt_eq,
   H_tgt_eq_type ← get_local `H_tgt_eq >>= infer_type,
   s ← join_user_simp_lemmas true [`cgsimp],
   (H_tgt_eq_new_type, pr) ← simplify s H_tgt_eq_type {},
   get_local `H_tgt_eq >>= λ H_tgt_eq, replace_hyp H_tgt_eq H_tgt_eq_new_type pr,
   get_local `H_tgt_eq >>= subst,
   applyc `certigrad.backprop_correct,
   trace "nodup tgts nodes",
     solve1 cgsimp,
   trace "at_idx...",
     solve1 cgsimp,
   trace "well_formed_at...",
     solve1 (constructor >> all_goals cgsimp),
   trace "grads_exist_at...",
     solve1 (cgsimp),
   trace "pdfs_exist_at...",
     solve1 cgsimp,
   trace "is_gintegrable...",
     solve1 (cgsimp >> prove_is_mvn_integrable),
   trace "can_diff_under_ints...",
     solve1 (cgsimp >> prove_is_mvn_uintegrable),
   trace "prove_for_tgt done"

meta def prove_model_ok : tactic unit :=
do -- unfold lets
   whnf_target,
   -- introduce hypotheses
   [tgt, idx, H_at_idx] ← intros | fail "can't intro hyps",
   -- repeated case-analysis on idx
   forall_idxs prove_model_base (prove_goal_async prove_model_step) idx


end tactic
end certigrad
