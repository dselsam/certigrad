/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Proof that the simple, non-memoized version of stochastic backpropagation
is correct.
-/
import .graph .estimators .predicates .compute_grad .lemmas .tgrads .tactics .is_gdifferentiable

namespace certigrad
namespace theorems
open list

lemma compute_grad_slow_correct {costs : list ID} :
  ∀ {nodes : list node} {inputs : env} {tgt : reference},
  well_formed_at costs nodes inputs tgt →
  grads_exist_at nodes inputs tgt →
  pdfs_exist_at nodes inputs →
  is_gdifferentiable (λ m, ⟦sum_costs m costs⟧) tgt inputs nodes dvec.head →
  is_nabla_gintegrable (λ m, ⟦sum_costs m costs⟧) tgt inputs nodes dvec.head →
  is_gintegrable (λ m, ⟦compute_grad_slow costs nodes m tgt⟧) inputs nodes dvec.head →
  can_differentiate_under_integrals costs nodes inputs tgt →
  ∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m costs⟧) (env.insert tgt θ₀ inputs) nodes) dvec.head) (env.get tgt inputs)
  =
  E (graph.to_dist (λ m, ⟦compute_grad_slow costs nodes m tgt⟧) inputs nodes) dvec.head
| [] inputs tgt :=
assume (H_wf : well_formed_at costs [] inputs tgt)
       (H_gs_exist : grads_exist_at [] inputs tgt)
       (H_pdfs_exist : pdfs_exist_at [] inputs)
       (H_gdiff : true)
       (H_nabla_gint : true)
       (H_grad_gint : true)
       (H_diff_under_int : true),
begin
dunfold graph.to_dist,
simp [E.E_ret],
dunfold dvec.head compute_grad_slow sum_costs,
rw T.grad_sumr _ _ _ (sum_costs_differentiable costs tgt inputs),
apply congr_arg,
apply map_congr_fn_pred,
intros cost H_cost_in_costs,
assertv H_em : tgt = (cost, []) ∨ tgt ≠ (cost, []) := decidable.em _,
cases H_em with H_eq H_neq,
-- case 1: tgt = (cost, [])
{ rw H_eq, simp [env.get_insert_same, T.grad_id] },
-- case 2: tgt ≠ (cost, [])
{ simp [λ (x : T tgt.2), env.get_insert_diff x inputs (ne.symm H_neq), H_neq, T.grad_const] }
end

| (⟨ref, parents, operator.det op⟩ :: nodes) inputs tgt :=
assume H_wf H_gs_exist H_pdfs_exist H_gdiff H_nabla_gint H_grad_gint H_diff_under_int,

let θ := env.get tgt inputs in
let x := op^.f (env.get_ks parents inputs) in
let next_inputs := env.insert ref x inputs in

-- 0. Collect useful helpers
have H_ref_in_refs : ref ∈ ref :: map node.ref nodes, from mem_of_cons_same,

have H_ref_notin_parents : ref ∉ parents, from ref_notin_parents H_wf^.ps_in_env H_wf^.uids,

have H_tgt_neq_ref : tgt ≠ ref, from ref_ne_tgt H_wf^.m_contains_tgt H_wf^.uids,

have H_get_ks_next_inputs : env.get_ks parents next_inputs = env.get_ks parents inputs,
  begin dsimp, rw (env.get_ks_insert_diff H_ref_notin_parents) end,

have H_get_ref_next : env.get ref next_inputs = op^.f (env.get_ks parents inputs),
  begin dsimp, rw env.get_insert_same end,

have H_can_insert : env.get tgt next_inputs = env.get tgt inputs,
  begin dsimp, rw (env.get_insert_diff _ _ H_tgt_neq_ref) end,

have H_insert_next : ∀ (y : T ref.2), env.insert ref y inputs = env.insert ref y next_inputs,
  begin intro y, dsimp, rw env.insert_insert_same end,

have H_wfs : well_formed_at costs nodes next_inputs tgt ∧ well_formed_at costs nodes next_inputs ref, from wf_at_next H_wf,
have H_gs_exist_tgt : grads_exist_at nodes next_inputs tgt, from H_gs_exist^.left,
have H_pdfs_exist_next : pdfs_exist_at nodes next_inputs, from H_pdfs_exist,

have H_grad_gint_tgt : is_gintegrable (λ m, ⟦compute_grad_slow costs nodes m tgt⟧) next_inputs nodes dvec.head, from
  (iff.mpr (is_gintegrable_k_add _ _ _ _) H_grad_gint)^.left,

have H_nabla_gint_tgt : is_nabla_gintegrable (λ m, ⟦sum_costs m costs⟧) tgt next_inputs nodes dvec.head, from H_nabla_gint^.left,

have H_grad_gint₁ : is_gintegrable (λ (m : env), ⟦compute_grad_slow costs nodes m tgt⟧)
                             (env.insert ref (det.op.f op (env.get_ks parents inputs)) inputs)
                             nodes
                             dvec.head,
  begin dunfold is_gintegrable compute_grad_slow at H_grad_gint, apply (iff.mpr (is_gintegrable_k_add _ _ _ _) H_grad_gint)^.left end,

have H_grad_gint₂ : is_gintegrable
    (λ (m : env),
       ⟦sumr
         (map
            (λ (idx : ℕ),
               det.op.pb op (env.get_ks parents m) (env.get ref m) (compute_grad_slow costs nodes m ref) idx (tgt.snd))
            (filter (λ (idx : ℕ), tgt = dnth parents idx) (riota (length parents))))⟧)
    (env.insert ref (det.op.f op (env.get_ks parents inputs)) inputs)
    nodes
    dvec.head,
    begin dunfold is_gintegrable compute_grad_slow at H_grad_gint, apply (iff.mpr (is_gintegrable_k_add _ _ _ _) H_grad_gint)^.right end,

begin
dunfold graph.to_dist operator.to_dist compute_grad_slow,
simp [E.E_bind, E.E_ret],
dunfold dvec.head,
rw E.E_k_add _ _ _ _ H_grad_gint₁ H_grad_gint₂,
simp only,
rw E.E_k_sum_map _ _ nodes _ H_pdfs_exist H_grad_gint₂,

-- 1. Use the general estimator on the LHS
pose g := (λ (v : dvec T parents^.p2) (θ : T tgt.2), E (graph.to_dist (λ (m : env), ⟦sum_costs m costs⟧) (env.insert ref (det.op.f op v) (env.insert tgt θ inputs)) nodes) dvec.head),
assert H_diff₁ : T.is_cdifferentiable (λ (θ₀ : T (tgt.snd)), g (env.get_ks parents (env.insert tgt θ inputs)) θ₀) θ,
  { exact H_gdiff^.left },

assert H_diff₂ : T.is_cdifferentiable (λ (θ₀ : T (tgt.snd)), sumr (map (λ (idx : ℕ), g (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ inputs)) idx) θ)
                                                                 (filter (λ (idx : ℕ), tgt = dnth parents idx) (riota (length parents)))))
                                      θ,
  { exact H_gdiff^.right^.left },

rw (T.multiple_args_general parents tgt inputs g θ H_diff₁ H_diff₂),
dsimp,

-- 2. Make the first terms equal, recursively
simp [env.insert_get_same H_wf^.m_contains_tgt],

pose H_almost_tgt := (eq.symm (compute_grad_slow_correct H_wfs^.left H_gs_exist_tgt H_pdfs_exist_next H_gdiff^.right^.right^.left H_nabla_gint_tgt H_grad_gint_tgt H_diff_under_int^.left)),
rw (env.get_insert_diff _ _ H_tgt_neq_ref) at H_almost_tgt,
erw H_almost_tgt,
dsimp,
simp [λ (θ : T tgt.2), env.insert_insert_flip x θ inputs (ne.symm H_tgt_neq_ref)],
apply congr_arg,

-- 3. Time for the second term: get rid of sum and use map_filter_congr
apply (congr_arg sumr),
apply map_filter_congr,
intros idx H_idx_in_riota H_tgt_dnth_parents_idx,
assertv H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_dnth_parents_idx⟩,
assertv H_tshape_at_idx : at_idx parents^.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx,
assertv H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx,

-- 4. Put the LHS in terms of T.tmulT
rw (T.grad_chain_rule (λ (θ : T tgt.2), det.op.f op (dvec.update_at θ (env.get_ks parents inputs) idx))
                      (λ (x : T ref.2), E (graph.to_dist (λ (m : env), ⟦sum_costs m costs⟧)
                                                         (env.insert ref x inputs)
                                                         nodes)
                                           dvec.head)),

-- 5. Replace `m` with `inputs`/`next_inputs` so that we can use `pb_correct`
assert H_swap_m_for_inputs :
graph.to_dist (λ (m : env),
                   ⟦op^.pb (env.get_ks parents m)
                           (env.get ref m)
                           (compute_grad_slow costs nodes m ref)
                           idx
                           tgt.2⟧)
                next_inputs
                nodes
=
(graph.to_dist (λ (m : env),
                    ⟦op^.pb (env.get_ks parents next_inputs)
                            x
                            (compute_grad_slow costs nodes m ref)
                            idx
                            tgt.2⟧)
                 next_inputs
                 nodes),
begin
  apply graph.to_dist_congr,
  exact H_wfs^.right^.uids,
  dsimp,
  intros m H_envs_match,
  apply dvec.singleton_congr,
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
  simp [H_parents_match, H_ref_matches],
end,

rw H_swap_m_for_inputs,
clear H_swap_m_for_inputs,

-- 6. Use pb_correct
assertv H_f_pre : op^.pre (env.get_ks parents next_inputs) := eq.rec_on (eq.symm H_get_ks_next_inputs) (H_gs_exist^.right H_tgt_in_parents)^.left,
simp [λ (m : env), op^.pb_correct (env.get_ks parents next_inputs) x (by rw H_get_ks_next_inputs) (compute_grad_slow costs nodes m ref) H_tshape_at_idx H_f_pre],

-- 7. Push E over tmulT and cancel the first terms
simp [E.E_k_tmulT, H_get_ks_next_inputs, env.dvec_get_get_ks inputs H_tgt_at_idx],
apply congr_arg,

-- 8. Final recursive case
assertv H_gs_exist_ref : grads_exist_at nodes next_inputs ref := (H_gs_exist^.right H_tgt_in_parents)^.right,

assert H_grad_gint_ref : is_gintegrable (λ m, ⟦compute_grad_slow costs nodes m ref⟧) next_inputs nodes dvec.head,
begin
assertv H_op_called : is_gintegrable (λ m, ⟦det.op.pb op (env.get_ks parents m) (env.get ref m) (compute_grad_slow costs nodes m ref) idx (tgt.snd)⟧)
                                    next_inputs nodes dvec.head :=
  is_gintegrable_of_sumr_map (λ m idx, det.op.pb op (env.get_ks parents m) (env.get ref m) (compute_grad_slow costs nodes m ref) idx (tgt.snd))
                                    next_inputs nodes _ H_grad_gint₂ idx (in_filter _ _ _ H_idx_in_riota H_tgt_dnth_parents_idx),

assert H_op_called_swap : is_gintegrable (λ m, ⟦det.op.pb op (env.get_ks parents next_inputs) x (compute_grad_slow costs nodes m ref) idx (tgt.snd)⟧)
                                         next_inputs nodes dvec.head,
{
apply is_gintegrable_k_congr _ _ _ _ _ H_wfs^.right^.uids _ H_op_called,
intros m H_envs_match,
-- TODO(dhs): this is copy-pasted from above
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
},

simp only [λ (m : env), op^.pb_correct (env.get_ks parents next_inputs) x (by rw H_get_ks_next_inputs) (compute_grad_slow costs nodes m ref) H_tshape_at_idx H_f_pre] at H_op_called_swap,
exact iff.mpr (is_gintegrable_tmulT _ _ _ _) H_op_called_swap
end,

assert H_gdiff_ref : is_gdifferentiable (λ m, ⟦sum_costs m costs⟧) ref next_inputs nodes dvec.head,
  { exact H_gdiff^.right^.right^.right H_idx_in_riota H_tgt_dnth_parents_idx },

assert H_nabla_gint_ref : is_nabla_gintegrable (λ m, ⟦sum_costs m costs⟧) ref next_inputs nodes dvec.head,
  { exact H_nabla_gint^.right H_idx_in_riota H_tgt_dnth_parents_idx },

pose H_correct_ref := compute_grad_slow_correct H_wfs^.right H_gs_exist_ref H_pdfs_exist_next
                                                H_gdiff_ref H_nabla_gint_ref H_grad_gint_ref (H_diff_under_int^.right H_tgt_in_parents),

simp [H_get_ref_next] at H_correct_ref,
dsimp at H_correct_ref,
simp [env.insert_insert_same] at H_correct_ref,
dsimp,
simp [env.dvec_update_at_env inputs H_tgt_at_idx],
exact H_correct_ref
end

| (⟨ref, parents, operator.rand op⟩ :: nodes) inputs tgt :=
assume H_wf H_gs_exist H_pdfs_exist H_gdiff H_nabla_gint H_grad_gint H_diff_under_int,

let θ := env.get tgt inputs in
let next_inputs := λ (y : T ref.2), env.insert ref y inputs in

-- 0. Collect useful helpers
have H_ref_in_refs : ref ∈ ref :: map node.ref nodes, from mem_of_cons_same,
have H_ref_notin_parents : ref ∉ parents, from ref_notin_parents H_wf^.ps_in_env H_wf^.uids,
have H_tgt_neq_ref : tgt ≠ ref, from ref_ne_tgt H_wf^.m_contains_tgt H_wf^.uids,
have H_insert_θ : env.insert tgt θ inputs = inputs, by rw env.insert_get_same H_wf^.m_contains_tgt,

have H_parents_match : ∀ y, env.get_ks parents (next_inputs y) = env.get_ks parents inputs,
  begin intro y, dsimp, rw (env.get_ks_insert_diff H_ref_notin_parents), end,

have H_can_insert_y : ∀ y, env.get tgt (next_inputs y) = env.get tgt inputs,
  begin intro y, dsimp, rw (env.get_insert_diff _ _ H_tgt_neq_ref) end,

have H_wfs : ∀ y, well_formed_at costs nodes (next_inputs y) tgt ∧ well_formed_at costs nodes (next_inputs y) ref,
  from assume y, wf_at_next H_wf,

have H_parents_match : ∀ y, env.get_ks parents (next_inputs y) = env.get_ks parents inputs,
  begin intro y, dsimp, rw (env.get_ks_insert_diff H_ref_notin_parents), end,

have H_can_insert_y : ∀ y, env.get tgt (next_inputs y) = env.get tgt inputs,
  begin intro y, dsimp, rw (env.get_insert_diff _ _ H_tgt_neq_ref) end,

have H_op_pre : op^.pre (env.get_ks parents inputs), from H_pdfs_exist^.left,

begin
dunfold graph.to_dist operator.to_dist,
simp [E.E_bind],

-- 1. Rewrite with the hybrid estimator
definev g : T ref.2 → T tgt.2 → ℝ :=
  (λ (x : T ref.2) (θ₀ : T tgt.2),
      E (graph.to_dist (λ (m : env), ⟦sum_costs m costs⟧)
                       (env.insert ref x (env.insert tgt θ₀ inputs))
                       nodes)
        dvec.head),

definev θ : T tgt.2 := env.get tgt inputs,

assert H_diff₁ : T.is_cdifferentiable (λ (θ₀ : T (tgt.snd)), E (sprog.prim op (env.get_ks parents (env.insert tgt θ inputs))) (λ (y : dvec T [ref.snd]), g y^.head θ₀)) θ,
  { exact H_gdiff^.left },

assert H_diff₂ : T.is_cdifferentiable (λ (θ₀ : T (tgt.snd)), sumr (map (λ (idx : ℕ),
                                                                         E (sprog.prim op (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ inputs)) idx))
                                                                           (λ (y : dvec T [ref.snd]), g y^.head θ))
                                                                      (filter (λ (idx : ℕ), tgt = dnth parents idx) (riota (length parents))))) θ,
  { exact H_gdiff^.right^.left },

assert H_eint₁ : E.is_eintegrable (sprog.prim op (env.get_ks parents (env.insert tgt θ inputs))) (λ (x : dvec T [ref.snd]), ∇ (g x^.head) θ),
begin
dsimp [E.is_eintegrable, dvec.head],
simp only [env.insert_get_same H_wf^.m_contains_tgt],
exact H_nabla_gint^.left
end,

assert H_eint₂ : E.is_eintegrable (sprog.prim op (env.get_ks parents (env.insert tgt θ inputs)))
    (λ (x : dvec T [ref.snd]),
       sumr
         (map
            (λ (idx : ℕ),
               g x^.head θ ⬝ ∇
                 (λ (θ₀ : T (tgt.snd)),
                    T.log
                      (rand.op.pdf op (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ inputs)) idx)
                         (dvec.head x)))
                 θ)
            (filter (λ (idx : ℕ), tgt = dnth parents idx) (riota (length parents))))),
begin
dsimp [E.is_eintegrable, dvec.head],
simp only [env.insert_get_same H_wf^.m_contains_tgt],
exact H_nabla_gint^.right^.left,
end,

assert H_g_diff : ∀ (x : T (ref.snd)), T.is_cdifferentiable (g x) θ,
begin
  intros y,
  dsimp,
  simp [λ θ₀, env.insert_insert_flip y θ₀ inputs (ne.symm H_tgt_neq_ref)],
  simp [eq.symm (H_can_insert_y y)],
  apply pd_is_cdifferentiable _ _ _ _ (H_wfs _)^.left (H_gs_exist^.right _) (H_pdfs_exist^.right _) (H_diff_under_int^.right _)
end,

assertv H_g_uint : T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)), rand.op.pdf op (env.get_ks parents (env.insert tgt θ inputs)) x ⬝ g x θ₀) θ :=
  H_diff_under_int^.left^.left^.right,

assertv H_g_grad_uint : T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)), ∇ (λ (θ₁ : T (tgt.snd)), rand.op.pdf op (env.get_ks parents (env.insert tgt θ inputs)) x ⬝ g x θ₁) θ₀) θ :=
  H_diff_under_int^.left^.right^.left^.right,

assert H_d'_pdf_cdiff: ∀ (idx : ℕ), at_idx parents idx tgt →
    ∀ (v : T (ref.snd)), T.is_cdifferentiable (λ (x₀ : T (tgt.snd)), rand.op.pdf op (dvec.update_at x₀ (env.get_ks parents (env.insert tgt θ inputs)) idx) v) θ,
begin
  intros idx H_at_idx y,
  assertv H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_at_idx,
  assertv H_pre_satisfied : op^.pre (env.get_ks parents inputs) := H_gs_exist^.left H_tgt_in_parents,
  simp [H_insert_θ],
  dunfold E, dsimp,
  simp [eq.symm (env.dvec_get_get_ks inputs H_at_idx)],
  exact (op^.pdf_cdiff (at_idx_p2 H_at_idx) H_pre_satisfied)
end,

assertv H_d'_uint : ∀ (idx : ℕ), at_idx parents idx tgt →
    T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)), rand.op.pdf op (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ inputs)) idx) x ⬝ g x θ) θ := H_diff_under_int^.left^.right^.right^.left,

assertv H_d'_grad_uint : ∀ (idx : ℕ),  at_idx parents idx tgt →
    T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)),
                                         ∇ (λ (θ₀ : T (tgt.snd)), rand.op.pdf op (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ inputs)) idx) x ⬝ g x θ) θ₀) θ :=
H_diff_under_int^.left^.right^.right^.right,

dsimp,
rw (estimators.hybrid_general inputs H_wf^.m_contains_tgt op H_op_pre g θ rfl
                              H_g_diff H_g_uint H_g_grad_uint
                              H_d'_pdf_cdiff H_d'_uint H_d'_grad_uint H_diff₁ H_diff₂ H_eint₁ H_eint₂),

-- 2. Cancel first stochastic choice
dsimp,
simp [env.insert_get_same H_wf^.m_contains_tgt],
apply congr_arg,
apply funext,
intro y,
cases y with ignore y ignore dnil,
cases dnil,
dunfold dvec.head,

assert H_get_ks_next_inputs : env.get_ks parents (next_inputs y) = env.get_ks parents inputs,
  begin dsimp, rw (env.get_ks_insert_diff H_ref_notin_parents) end,

assert H_get_ref_next : env.get ref (next_inputs y) = y,
  begin dsimp, rw env.get_insert_same end,

-- 3. Push E over sum on RHS
dunfold compute_grad_slow,
assert H_grad_gint₁ : is_gintegrable (λ (m : env), ⟦compute_grad_slow costs nodes m tgt⟧) (env.insert ref y inputs) nodes dvec.head,
 { dsimp [is_gintegrable, compute_grad_slow] at H_grad_gint, apply (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_grad_gint^.right y))^.left },

assert H_grad_gint₂ : is_gintegrable
    (λ (m : env),
       ⟦sumr
         (map
            (λ (idx : ℕ),
               sum_downstream_costs nodes costs ref m ⬝ rand.op.glogpdf op (env.get_ks parents m) (env.get ref m) idx
                 (tgt.snd))
            (filter (λ (idx : ℕ), tgt = dnth parents idx) (riota (length parents))))⟧)
    (env.insert ref y inputs)
    nodes
    dvec.head,
  { dsimp [is_gintegrable, compute_grad_slow] at H_grad_gint, apply (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_grad_gint^.right y))^.right },

rw E.E_k_add _ _ _ _ H_grad_gint₁ H_grad_gint₂,

-- 4. Cancel the first terms
assert H_gdiff_tgt : is_gdifferentiable (λ (m : env), ⟦sum_costs m costs⟧) tgt (next_inputs y) nodes dvec.head,
  { exact H_gdiff^.right^.right y },

assert H_grad_gint_tgt : is_gintegrable (λ (m : env), ⟦compute_grad_slow costs nodes m tgt⟧) (next_inputs y) nodes dvec.head,
  { exact (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_grad_gint^.right y))^.left },

assert H_nabla_gint_tgt : is_nabla_gintegrable (λ m, ⟦sum_costs m costs⟧) tgt (next_inputs y) nodes dvec.head,
  { exact H_nabla_gint^.right^.right y },

-- TODO(dhs): confirm ERW is only needed because of the `definev`
erw -(compute_grad_slow_correct (H_wfs _)^.left (H_gs_exist^.right y) (H_pdfs_exist^.right _) H_gdiff_tgt H_nabla_gint_tgt H_grad_gint_tgt (H_diff_under_int^.right y)),
dsimp,

simp [λ (θ : T tgt.2), env.insert_insert_flip θ y inputs H_tgt_neq_ref],
rw (env.get_insert_diff _ _ H_tgt_neq_ref),
apply congr_arg,

-- 5. Push E over sumr and expose map

rw E.E_k_sum_map _ _ _ _ (H_pdfs_exist^.right _) H_grad_gint₂,
apply congr_arg,

-- 6. Apply map_filter_congr
exact map_filter_expand_helper _ _ _ _ _ _ H_wf H_gs_exist _
end
end theorems
end certigrad
