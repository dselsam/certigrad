/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Miscellaneous lemmas.
-/
import .predicates .tcont .expected_value .lemmas .compute_grad_slow_correct

namespace certigrad
open list

lemma is_nabla_gintegrable_of_gintegrable {costs : list ID} :
  Π (m : env) (nodes : list node) (tgt : reference),
  well_formed_at costs nodes m tgt →
  grads_exist_at nodes m tgt →
  pdfs_exist_at nodes m →
  is_gdifferentiable (λ m, ⟦sum_costs m costs⟧) tgt m nodes dvec.head →
  can_differentiate_under_integrals costs nodes m tgt →

  is_gintegrable (λ m, ⟦compute_grad_slow costs nodes m tgt⟧) m nodes dvec.head → is_nabla_gintegrable (λ m, ⟦sum_costs m costs⟧) tgt m nodes dvec.head
| m [] tgt H_wf H_gs_exist H_pdfs_exist H_gdiff H_diff_under_int H_gint := trivial

| m (⟨ref, parents, operator.det op⟩ :: nodes) tgt H_wf H_gs_exist H_pdfs_exist H_gdiff H_diff_under_int H_gint :=
let x : T ref.2 := op^.f (env.get_ks parents m),
    next_inputs : env := env.insert ref x m in
have H_ref_notin_parents : ref ∉ parents, from ref_notin_parents H_wf^.ps_in_env H_wf^.nodup,
have H_get_ks_next_inputs : env.get_ks parents next_inputs = env.get_ks parents m,
  begin dsimp, rw (env.get_ks_insert_diff H_ref_notin_parents) end,
have H_wfs : well_formed_at costs nodes next_inputs tgt ∧ well_formed_at costs nodes next_inputs ref, from wf_at_next H_wf,

begin
dsimp [is_gintegrable, compute_grad_slow] at H_gint,
dsimp [is_nabla_gintegrable],
split,
-- tgt
begin
apply is_nabla_gintegrable_of_gintegrable,
exact H_wfs^.left,
exact H_gs_exist^.left,
exact H_pdfs_exist,
exact H_gdiff^.right^.right^.left,
exact H_diff_under_int^.left,
exact (iff.mpr (is_gintegrable_k_add _ _ _ _) H_gint)^.left
end,

-- ref
begin
intros idx H_idx_in_riota H_tgt_eq_dnth_idx,
assertv H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_eq_dnth_idx⟩,
assertv H_tshape_at_idx : at_idx parents^.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx,
assertv H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx,
assertv H_f_pre : op^.pre (env.get_ks parents next_inputs) := eq.rec_on (eq.symm H_get_ks_next_inputs) (H_gs_exist^.right H_tgt_in_parents)^.left,

-- TODO(dhs): copy-pasted from compute_grad_slow_correct.lean:223
assert H_grad_gint_ref : is_gintegrable (λ m, ⟦compute_grad_slow costs nodes m ref⟧) next_inputs nodes dvec.head,
begin
assertv H_op_called : is_gintegrable (λ m, ⟦det.op.pb op (env.get_ks parents m) (env.get ref m) (compute_grad_slow costs nodes m ref) idx (tgt.snd)⟧)
                                    next_inputs nodes dvec.head :=
  is_gintegrable_of_sumr_map (λ m idx, det.op.pb op (env.get_ks parents m) (env.get ref m) (compute_grad_slow costs nodes m ref) idx (tgt.snd))
                                    next_inputs nodes _ (iff.mpr (is_gintegrable_k_add _ _ _ _) H_gint)^.right idx (in_filter _ _ _ H_idx_in_riota H_tgt_eq_dnth_idx),

assert H_op_called_swap : is_gintegrable (λ m, ⟦det.op.pb op (env.get_ks parents next_inputs) x (compute_grad_slow costs nodes m ref) idx (tgt.snd)⟧)
                                         next_inputs nodes dvec.head,
begin
apply is_gintegrable_k_congr _ _ _ _ _ H_wfs^.right^.nodup _ H_op_called,
intros m H_envs_match,
-- TODO(dhs): this is copy-pasted from above (nested comment!)
assert H_parents_match : env.get_ks parents m = env.get_ks parents next_inputs,
begin
  apply env.get_ks_env_eq,
  intros parent H_parent_in_parents,
  apply H_envs_match,
  apply env.has_key_insert,
  exact (H_wf^.ps_in_env^.left parent H_parent_in_parents)
end,
assert H_ref_matches : env.get ref m = x,
begin
  assertv H_env_has_key_ref : env.has_key ref next_inputs := env.has_key_insert_same _ _,
  rw [H_envs_match ref H_env_has_key_ref, env.get_insert_same]
end,
simp only [H_parents_match, H_ref_matches],
end,

simp only [λ (m : env), op^.pb_correct (env.get_ks parents next_inputs) x (by rw H_get_ks_next_inputs) (compute_grad_slow costs nodes m ref) H_tshape_at_idx H_f_pre] at H_op_called_swap,
exact iff.mpr (is_gintegrable_tmulT _ _ _ _) H_op_called_swap
end,
apply is_nabla_gintegrable_of_gintegrable,
exact H_wfs^.right,
exact (H_gs_exist^.right H_tgt_in_parents)^.right,
exact H_pdfs_exist,
exact H_gdiff^.right^.right^.right H_idx_in_riota H_tgt_eq_dnth_idx,
exact H_diff_under_int^.right H_tgt_in_parents,
exact H_grad_gint_ref
end
end

| inputs (⟨ref, parents, operator.rand op⟩ :: nodes) tgt H_wf H_gs_exist H_pdfs_exist H_gdiff H_diff_under_int H_gint :=
let θ := env.get tgt inputs in
let next_inputs := λ (y : T ref.2), env.insert ref y inputs in
have H_tgt_in_keys : tgt ∈ env.keys inputs, from env.has_key_mem_keys H_wf^.m_contains_tgt,
have H_ref_in_refs : ref ∈ ref :: map node.ref nodes, from mem_of_cons_same,
have H_ref_notin_parents : ref ∉ parents, from ref_notin_parents H_wf^.ps_in_env H_wf^.nodup,
have H_tgt_neq_ref : tgt ≠ ref, from nodup_append_neq H_tgt_in_keys H_ref_in_refs H_wf^.nodup,

have H_wfs : ∀ y, well_formed_at costs nodes (next_inputs y) tgt ∧ well_formed_at costs nodes (next_inputs y) ref,
  from assume y, wf_at_next H_wf,

begin
dsimp [is_gintegrable, compute_grad_slow] at H_gint,
dsimp [is_nabla_gintegrable],

assert H_cgsc : ∀ x,
E (graph.to_dist (λ (m : dmap (ID × list ℕ) (λ (ref : ID × list ℕ), T (ref.snd))), ⟦compute_grad_slow costs nodes m tgt⟧)
                 (env.insert ref x inputs) nodes)
  dvec.head
=
∇ (λ (θ₀ : T (tgt.snd)),
     E (graph.to_dist (λ (m : dmap (ID × list ℕ) (λ (ref : ID × list ℕ), T (ref.snd))), ⟦sum_costs m costs⟧)
                      (env.insert ref x (env.insert tgt θ₀ inputs)) nodes)
        dvec.head)
  (env.get tgt inputs),
begin -- start H_cgsc
intro x,
rw -theorems.compute_grad_slow_correct (H_wfs x)^.left (H_gs_exist^.right _) (H_pdfs_exist^.right _) (H_gdiff^.right^.right _)
                                       _
                                       (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_gint^.right x))^.left
                                       (H_diff_under_int^.right _),

simp only [(λ (θ₀ : T tgt.2), env.insert_insert_flip θ₀ x inputs H_tgt_neq_ref), @env.get_insert_diff tgt ref x inputs H_tgt_neq_ref],
exact is_nabla_gintegrable_of_gintegrable _ _ _ (H_wfs x)^.left (H_gs_exist^.right _) (H_pdfs_exist^.right _) (H_gdiff^.right^.right _)
                                          (H_diff_under_int^.right _)
                                          (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_gint^.right x))^.left,
end, -- end H_cgsc

simp only [λ x, E.E_k_add _ _ _ _ (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_gint^.right x))^.left
                              (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_gint^.right x))^.right] at H_gint,
simp only [H_cgsc] at H_gint,

-- TODO(dhs): apply and.intro _ (and.intro _ _) does not instantiate the second metavariable, change back once fixed
split, tactic.swap, split, tactic.rotate 2,

begin -- start PD
apply (iff.mpr (T.is_integrable_add_middle _ _ _) H_gint^.left)^.left
end, -- end PD

dunfold sum_downstream_costs at H_gint,

-- Scores
assert H_score_rw : ∀ y,
map
            (λ (idx : ℕ),
               E
                 (graph.to_dist
                    (λ (m : dmap (ID × list ℕ) (λ (ref : ID × list ℕ), T (ref.snd))), ⟦sum_costs m costs⟧)
                    (env.insert ref y inputs)
                    nodes)
                 dvec.head ⬝ ∇
                 (λ (θ₀ : T (tgt.snd)), T.log (rand.op.pdf op (dvec.update_at θ₀ (env.get_ks parents inputs) idx) y))
                 (env.get tgt inputs))
            (filter (λ (idx : ℕ), tgt = dnth parents idx) (riota (length parents)))
=
map
    (λ (idx : ℕ),
       E
         (graph.to_dist
            (λ (m : env),
               ⟦sum_downstream_costs nodes costs ref m ⬝ rand.op.glogpdf op (env.get_ks parents m) (env.get ref m)
                    idx
                    (tgt.snd)⟧)
            (env.insert ref y inputs)
            nodes)
         dvec.head)
    (filter (λ (idx : ℕ), tgt = dnth parents idx) (riota (length parents))),
begin -- start H_score_rw
exact map_filter_expand_helper _ _ _ _ _ _ H_wf H_gs_exist
end, -- end H_score_rw

assert H_pull_E : ∀ y,
sumr
         (map
            (λ (idx : ℕ),
               E
                 (graph.to_dist
                    (λ (m : env),
                       ⟦sum_downstream_costs nodes costs ref m ⬝ rand.op.glogpdf op (env.get_ks parents m) (env.get ref m) idx (tgt.snd)⟧)
                    (env.insert ref y inputs)
                    nodes)
                 dvec.head)
            (filter (λ (idx : ℕ), tgt = dnth parents idx) (riota (length parents))))
=
E (graph.to_dist (λ (m : env),
                    ⟦sumr (map (λ (idx : ℕ), sum_downstream_costs nodes costs ref m ⬝ rand.op.glogpdf op (env.get_ks parents m) (env.get ref m) idx (tgt.snd))
                               (filter (λ (idx : ℕ), tgt = dnth parents idx) (riota (length parents))))⟧)
                    (env.insert ref y inputs)
                    nodes)
                 dvec.head,
begin -- start H_pull_E
intro y,
rw -E.E_g_pull_out_of_sum _ _ _ _ (H_pdfs_exist^.right y),
exact (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_gint^.right y))^.right
end, -- end H_pull_E

begin -- start score
simp only [H_score_rw], clear H_score_rw,
simp only [H_pull_E], clear H_pull_E,
apply (iff.mpr (T.is_integrable_add_middle _ _ _) H_gint^.left)^.right
end, -- end score

-- Recursive
begin
intro y,
apply is_nabla_gintegrable_of_gintegrable,
exact (H_wfs y)^.left,
exact H_gs_exist^.right _,
exact H_pdfs_exist^.right _,
exact H_gdiff^.right^.right _,
exact H_diff_under_int^.right _,
apply (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_gint^.right y))^.left,
end

end

end certigrad
