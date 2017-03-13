/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Proof that the memoization part of stochastic backpropagation is correct.
-/
import .graph .estimators .predicates .compute_grad

namespace certigrad
namespace theorems
open list

lemma step_congr (costs : list ID) (callback₁ callback₂ : list node → Π (tgt : reference), T tgt.2)
                 (nodes : list node) (m : env) (tgt : reference) :
   ∀ (n : node)
    (H_callback_tgt : callback₁ nodes tgt = callback₂ nodes tgt)
    (H_callback_node : callback₁ nodes n^.ref = callback₂ nodes n^.ref),
    compute_grad_step costs callback₁ (n::nodes) m tgt = compute_grad_step costs callback₂ (n::nodes) m tgt
| ⟨ref, parents, operator.det op⟩ :=
assume H_callback_tgt H_callback_node,
begin dunfold compute_grad_step, rw [H_callback_tgt, H_callback_node] end

| ⟨ref, parents, operator.rand op⟩ :=
assume H_callback_tgt H_callback_node,
begin dunfold compute_grad_step, rw [H_callback_tgt] end

lemma step_correct {costs : list ID} {callback : list node → Π (tgt : reference), T tgt.2}
              {nodes : list node} {m : env} {tgt : reference} :
  ∀ {n : node}
    (H_callback_tgt : callback nodes tgt = compute_grad_slow costs nodes m tgt)
    (H_callback_node : callback nodes n^.ref = compute_grad_slow costs nodes m n^.ref),
    compute_grad_step costs callback (n::nodes) m tgt = compute_grad_slow costs (n::nodes) m tgt

| ⟨ref, parents, operator.det op⟩ :=
assume H_callback_tgt H_callback_node,
begin dunfold compute_grad_step compute_grad_slow, rw [sumrd_sumr, H_callback_tgt, H_callback_node] end

| ⟨ref, parents, operator.rand op⟩ :=
assume H_callback_tgt H_callback_node,
begin dunfold compute_grad_step compute_grad_slow, rw [sumrd_sumr, H_callback_tgt] end

lemma strip_foldr_base {costs : list ID} {m : env} :
      Π {tgts : list reference} {tgt₀ : reference} {idx : ℕ},
        at_idx tgts idx tgt₀ →
       nodup tgts →
env.get tgt₀
         (foldr (λ (ref : reference) (dict₀ : env),
                    (env.insert ref
                                 (compute_grad_step costs (λ (nodes' : list node) (tgt' : reference), T.error "backprop-end") [] m ref)
                                 dict₀))
                 env.mk
                 tgts)
=
compute_grad_step costs (λ (nodes : list node) (ref : reference), env.get ref env.mk) [] m tgt₀
| [] _ _ H_at_idx _ := false.rec _ (nat.not_lt_zero _ H_at_idx^.left)

| (tgt::tgts) tgt₀ 0 H_at_idx H_nodup :=
have H_eq : tgt = tgt₀, from at_idx_inj at_idx_0 H_at_idx,
begin
rw -H_eq,
dunfold foldr,
rw env.get_insert_same,
reflexivity
end

| (tgt::tgts) tgt₀ (idx+1) H_at_idx H_nodup :=
have H_neq : tgt₀ ≠ tgt, from nodup_at_idx_neq H_nodup H_at_idx,
have H_at_idx_next : at_idx tgts idx tgt₀, from nodup_at_idx H_nodup H_at_idx,
begin
dunfold foldr,
rw (env.get_insert_diff _ _ H_neq),
exact (strip_foldr_base H_at_idx_next (nodup_of_nodup_cons H_nodup)),
end

lemma strip_foldr_step {costs : list ID} {nodes : list node} {m old_dict : env} :
  Π {tgts : list reference} {tgt₀ : reference} {idx : ℕ},
    at_idx tgts idx tgt₀ →
    nodup tgts →
    env.get tgt₀
             (foldr (λ (tgt' : reference) (dict' : env),
                       (env.insert tgt'
                                    (compute_grad_step costs (λ (nodes : list node) (ref : reference), env.get ref old_dict)
                                                       nodes m tgt')
                                    dict'))
                    env.mk
                    tgts)
    =
    compute_grad_step costs (λ (nodes : list node) (tgt : reference), env.get tgt old_dict) nodes m tgt₀
| [] _ _ H_idx _ := false.rec _ (nat.not_lt_zero _ H_idx^.left)

| (tgt::tgts) tgt₀ 0 H_at_idx H_nodup :=
begin
dunfold at_idx dnth at H_at_idx,
rw H_at_idx^.right,
dunfold foldr,
rw env.get_insert_same
end

| (tgt::tgts) tgt₀ (idx+1) H_at_idx H_nodup :=
have H_neq : tgt₀ ≠ tgt, from nodup_at_idx_neq H_nodup H_at_idx,
have H_at_idx_next : at_idx tgts idx tgt₀, from nodup_at_idx H_nodup H_at_idx,
begin
dunfold foldr,
rw env.get_insert_diff _ _ H_neq,
exact (strip_foldr_step H_at_idx_next (nodup_of_nodup_cons H_nodup)),
end

lemma memoize_correct {costs : list ID} :
  ∀ {nodes : list node} (m : env) {tgts : list reference},
  ∀ {tgt₀ : reference} {idx : ℕ}, at_idx tgts idx tgt₀ →
  ∀ {init_dict : env}, init_dict = compute_init_dict costs nodes tgts →
  nodup (tgts ++ map node.ref nodes) →
  env.get tgt₀ (backprop_core costs init_dict nodes m tgts)
  =
  compute_grad_slow costs nodes m tgt₀

| _ _ [] _ _ H_at_idx _ _ _ := false.rec _ (nat.not_lt_zero _ H_at_idx^.left)

| [] m (tgt::tgts) tgt₀ idx H_at_idx idict H_idict H_nodup :=
have H_nodup_tgts : nodup (tgt::tgts), from nodup_of_nodup_append_left H_nodup,
begin
rw H_idict,
dunfold backprop_core compute_init_dict,
rw (strip_foldr_base H_at_idx H_nodup_tgts),
dunfold compute_grad_step,
rw sumr_sumr₁,
reflexivity,
end

| (n::nodes) m (tgt::tgts) tgt₀ idx H_at_idx idict H_idict H_nodup :=
have H_nodup_tgts : nodup (tgt::tgts), from nodup_of_nodup_append_left H_nodup,
have H_nodup_n : nodup ((n^.ref :: tgt :: tgts) ++ map node.ref nodes), from nodup_append_swap H_nodup,
have H_at_idx_tgt₀ : at_idx (n^.ref :: tgt :: tgts) (idx+1) tgt₀, from at_idx_cons H_at_idx,
have H_at_idx_n : at_idx (n^.ref :: tgt :: tgts) 0 n^.ref, from at_idx_0,
begin
rw H_idict,
dunfold backprop_core compute_init_dict,
rw (strip_foldr_step H_at_idx H_nodup_tgts),
dunfold compute_grad_step compute_grad_slow,
apply step_correct,
apply (memoize_correct _ H_at_idx_tgt₀ rfl H_nodup_n),
apply (memoize_correct _ H_at_idx_n rfl H_nodup_n)
end

end theorems
end certigrad
