/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Miscellaneous lemmas.
-/
import .predicates .tcont .expected_value

namespace certigrad
open list

lemma ref_notin_parents {n : node} {nodes : list node} {m : env} :
  all_parents_in_env m (n::nodes) → uniq_ids (n::nodes) m → n^.ref ∉ n^.parents :=
begin
cases n with ref parents op,
intros H_ps_in_env H_uids H_ref_in_parents,
dsimp [uniq_ids] at H_uids,
dsimp at H_ref_in_parents,
dsimp [all_parents_in_env] at H_ps_in_env,
exact H_uids^.left (H_ps_in_env^.left ref H_ref_in_parents)
end

lemma ref_ne_tgt {n : node} {nodes : list node} {m : env} {tgt : reference} :
env.has_key tgt m → uniq_ids (n::nodes) m → tgt ≠ n^.ref :=
begin
cases n with ref parents op,
intros H_tgt H_uids H_eq,
dsimp [uniq_ids] at H_uids,
subst H_eq,
exact H_uids^.left H_tgt
end

lemma wf_at_next {costs : list ID} {n : node} {nodes : list node} {x : T n^.ref.2} {inputs : env} {tgt : reference} :
  let next_inputs : env := env.insert n^.ref x inputs in
  well_formed_at costs (n::nodes) inputs tgt → well_formed_at costs nodes next_inputs tgt ∧ well_formed_at costs nodes next_inputs n^.ref :=
begin
intros next_inputs H_wf,
cases n with ref parents op,
assertv H_uids_next : uniq_ids nodes next_inputs := H_wf^.uids^.right x,
assertv H_ps_in_env_next : all_parents_in_env next_inputs nodes := H_wf^.ps_in_env^.right x,
assertv H_costs_scalars_next : all_costs_scalars costs nodes := H_wf^.costs_scalars^.right,
assert H_m_contains_tgt : env.has_key tgt next_inputs,
  begin dsimp, apply env.has_key_insert, exact H_wf^.m_contains_tgt end,
assert H_m_contains_ref : env.has_key ref next_inputs,
  begin dsimp, apply env.has_key_insert_same end,
assertv H_cost_scalar_tgt : tgt.1 ∈ costs → tgt.2 = [] := H_wf^.tgt_cost_scalar,
assertv H_cost_scalar_ref : ref.1 ∈ costs → ref.2 = [] := H_wf^.costs_scalars^.left,
assertv H_wf_tgt : well_formed_at costs nodes next_inputs tgt :=
  ⟨H_uids_next, H_ps_in_env_next, H_costs_scalars_next, H_m_contains_tgt, H_cost_scalar_tgt⟩,
assertv H_wf_ref : well_formed_at costs nodes next_inputs ref :=
  ⟨H_uids_next, H_ps_in_env_next, H_costs_scalars_next, H_m_contains_ref, H_cost_scalar_ref⟩,
exact ⟨H_wf_tgt, H_wf_ref⟩
end

/-
lemma ref_notin_parents_alt : ∀ {n : node} {nodes : list node} {ref₀ : reference} {m : env},
  all_parents_in_env m (n::nodes) → ref₀ ∉ (env.keys m ++ map node.ref (n::nodes)) → ref₀ ∉ n^.parents
| ⟨ref, parents, op⟩ nodes ref₀ m H_ps_in_env H_ref₀_notin H_ref₀_in_parents :=
have H_ref₀_in : ref₀ ∈ env.keys m, from env.has_key_mem_keys (H_ps_in_env^.left _ H_ref₀_in_parents),
not_mem_of_not_mem_append_left H_ref₀_notin H_ref₀_in
-/

lemma pdfs_exist_at_ignore {ref₀ : reference} {x₁ x₂ : T ref₀.2} :
  ∀ {nodes : list node} {inputs : env},
     all_parents_in_env inputs nodes →
     (¬ env.has_key ref₀ inputs) → ref₀ ∉ map node.ref nodes →
     pdfs_exist_at nodes (env.insert ref₀ x₁ inputs) → pdfs_exist_at nodes (env.insert ref₀ x₂ inputs)
| [] _ _ _ _ _ := true.intro
| (⟨ref, parents, operator.det op⟩ :: nodes) inputs H_ps_in_env H_fresh₁ H_fresh₂ H_pdfs_exist_at :=
begin
dsimp [pdfs_exist_at] at H_pdfs_exist_at,
dsimp [pdfs_exist_at],
assertv H_ref₀_notin_parents : ref₀ ∉ parents := λ H_contra, H_fresh₁ (H_ps_in_env^.left ref₀ H_contra),
assert H_ref₀_neq_ref : ref₀ ≠ ref,
{ intro H_contra, subst H_contra, exact H_fresh₂ mem_of_cons_same },

rw env.get_ks_insert_diff H_ref₀_notin_parents,
rw env.insert_insert_flip _ _ _ (ne.symm H_ref₀_neq_ref),
rw env.get_ks_insert_diff H_ref₀_notin_parents at H_pdfs_exist_at,
rw env.insert_insert_flip _ _ _ (ne.symm H_ref₀_neq_ref) at H_pdfs_exist_at,


apply (pdfs_exist_at_ignore (H_ps_in_env^.right _) _ _ H_pdfs_exist_at),

{ intro H_contra, exact H_fresh₁ (env.has_key_insert_diff H_ref₀_neq_ref H_contra) },
{ exact not_mem_of_not_mem_cons H_fresh₂ }
end

| (⟨ref, parents, operator.rand op⟩ :: nodes) inputs H_ps_in_env H_fresh₁ H_fresh₂ H_pdfs_exist_at :=
begin
dsimp [pdfs_exist_at] at H_pdfs_exist_at,
dsimp [pdfs_exist_at],
assertv H_ref₀_notin_parents : ref₀ ∉ parents := λ H_contra, H_fresh₁ (H_ps_in_env^.left ref₀ H_contra),
assert H_ref₀_neq_ref : ref₀ ≠ ref,
{ intro H_contra, subst H_contra, exact H_fresh₂ mem_of_cons_same },
rw env.get_ks_insert_diff H_ref₀_notin_parents,
rw env.get_ks_insert_diff H_ref₀_notin_parents at H_pdfs_exist_at,

apply and.intro,
{ exact H_pdfs_exist_at^.left },
intro y,
note H_pdfs_exist_at_next := H_pdfs_exist_at^.right y,
rw env.insert_insert_flip _ _ _ (ne.symm H_ref₀_neq_ref),
rw env.insert_insert_flip _ _ _ (ne.symm H_ref₀_neq_ref) at H_pdfs_exist_at_next,

apply (pdfs_exist_at_ignore (H_ps_in_env^.right _) _ _ H_pdfs_exist_at_next),
{ intro H_contra, exact H_fresh₁ (env.has_key_insert_diff H_ref₀_neq_ref H_contra) },
{ exact not_mem_of_not_mem_cons H_fresh₂ }
end

lemma pdf_continuous {ref : reference} {parents : list reference} {op : rand.op parents^.p2 ref.2}
                     {nodes : list node} {inputs : env} {tgt : reference} :
  ∀ {idx : ℕ}, at_idx parents idx tgt →
  env.has_key tgt inputs →
  grads_exist_at (⟨ref, parents, operator.rand op⟩ :: nodes) inputs tgt →
  ∀ (y : T ref.2),
    T.is_continuous (λ (x : T tgt.2),
                      (op^.pdf (dvec.update_at x (env.get_ks parents (env.insert tgt (env.get tgt inputs) inputs)) idx) y))
                      (env.get tgt inputs) :=
begin
  intros idx H_at_idx H_tgt_in_inputs H_gs_exist y,
  assertv H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_at_idx,
  assertv H_pre_satisfied : op^.pre (env.get_ks parents inputs) := H_gs_exist^.left H_tgt_in_parents,
  simp [env.insert_get_same H_tgt_in_inputs],
  dsimp,
  simp [eq.symm (env.dvec_get_get_ks inputs H_at_idx)],
  exact (op^.cont (at_idx_p2 H_at_idx) H_pre_satisfied)
end

-- TODO(dhs): this will need to be `differentiable_of_grads_exist`
lemma continuous_of_grads_exist {costs : list ID} :
  Π {nodes : list node} {tgt : reference} {inputs : env},
  well_formed_at costs nodes inputs tgt →
  grads_exist_at nodes inputs tgt →
  T.is_continuous (λ (θ₀ : T tgt.2),
                    E (graph.to_dist (λ (env₀ : env), ⟦sum_costs env₀ costs⟧)
                                     (env.insert tgt θ₀ inputs)
                                     nodes)
                      dvec.head)
                 (env.get tgt inputs)
| [] tgt inputs H_wf_at H_gs_exist :=
begin
dunfold graph.to_dist,
simp [E.E_ret],
dunfold dvec.head sum_costs,
apply T.continuous_sumr,
intros cost H_cost_in_costs,
assertv H_em : (cost, []) = tgt ∨ (cost, []) ≠ tgt := decidable.em _,
cases H_em with H_eq H_neq,

-- case 1
begin
  cases tgt with tgt₁ tgt₂,
  injection H_eq with H_eq₁ H_eq₂,
  rw [H_eq₁, H_eq₂],
  dsimp,
  simp [env.get_insert_same],
  apply T.continuous_id,
end,

-- case 2
begin
  simp [λ (x₀ : T tgt.2), @env.get_insert_diff (cost, []) tgt x₀ inputs H_neq],
  apply T.continuous_const
end
end

| (⟨ref, parents, operator.det op⟩ :: nodes) tgt inputs H_wf H_gs_exist :=

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

begin
dunfold graph.to_dist,
simp [E.E_bind, E.E_ret],
dunfold operator.to_dist,
simp [E.E_ret],

assertv H_em_tgt_in_parents : tgt ∈ parents ∨ tgt ∉ parents := decidable.em _,
cases H_em_tgt_in_parents with H_tgt_in_parents H_tgt_notin_parents,
-- case 1
begin
definev chain₁ : T tgt.2 → T ref.2 :=
  λ (θ₀ : T tgt.2), op^.f (env.get_ks parents (env.insert tgt θ₀ inputs)),

definev chain₂ : T tgt.2 → T ref.2 → ℝ :=
  λ (θ₀ : T tgt.2) (x₀ : T ref.2),
     E (graph.to_dist (λ (env₀ : env), ⟦sum_costs env₀ costs⟧)
                      (env.insert ref x₀ (env.insert tgt θ₀ inputs))
                        nodes)
        dvec.head,

change T.is_continuous (λ (θ₀ : T tgt.2), chain₂ θ₀ (chain₁ θ₀)) (env.get tgt inputs),

assert H_chain₁ : T.is_continuous (λ (θ₀ : T tgt.2), chain₁ θ₀) (env.get tgt inputs),
begin
dsimp,
apply T.continuous_multiple_args,
intros idx H_at_idx,
simp [env.insert_get_same H_wf^.m_contains_tgt],
rw -(env.dvec_get_get_ks _ H_at_idx),
apply (op^.cont (env.get_ks parents inputs) (at_idx_p2 H_at_idx) (H_gs_exist^.right $ mem_of_at_idx H_at_idx)^.left),
end,

assert H_chain₂_θ : T.is_continuous (λ (x₀ : T tgt.2), chain₂ x₀ (chain₁ (env.get tgt inputs))) (env.get tgt inputs),
begin
dsimp,
simp [env.insert_get_same H_wf^.m_contains_tgt],
simp [λ (v₁ : T ref.2) (v₂ : T tgt.2) m, env.insert_insert_flip v₁ v₂ m (ne.symm H_tgt_neq_ref)],
rw -H_can_insert,
exact (continuous_of_grads_exist H_wfs^.left H_gs_exist_tgt)
end,

assert H_chain₂_f : T.is_continuous (chain₂ (env.get tgt inputs)) ((λ (θ₀ : T (tgt^.snd)), chain₁ θ₀) (env.get tgt inputs)),
begin
assertv H_gs_exist_ref : grads_exist_at nodes next_inputs ref := (H_gs_exist^.right H_tgt_in_parents)^.right,
dsimp,

simp [env.insert_get_same H_wf^.m_contains_tgt],
rw -H_get_ref_next,
simp [H_insert_next],

apply (continuous_of_grads_exist H_wfs^.right H_gs_exist_ref),
end,

exact (T.continuous_chain_full H_chain₁ H_chain₂_θ H_chain₂_f)
end,

-- case 2
begin
assert H_nodep_tgt : ∀ (θ₀ : T tgt.2), env.get_ks parents (env.insert tgt θ₀ inputs) = env.get_ks parents inputs,
begin intro θ₀, rw env.get_ks_insert_diff H_tgt_notin_parents end,
simp [H_nodep_tgt],
simp [λ (v₁ : T ref.2) (v₂ : T tgt.2) m, env.insert_insert_flip v₁ v₂ m (ne.symm H_tgt_neq_ref)],
rw -H_can_insert,
exact (continuous_of_grads_exist H_wfs^.left H_gs_exist_tgt)
end
end

| (⟨ref, parents, operator.rand op⟩ :: nodes) tgt inputs H_wf H_gs_exist :=

let θ := env.get tgt inputs in
let next_inputs := λ (y : T ref.2), env.insert ref y inputs in

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

have H_pdf_continuous : ∀ (y : T ref.2), T.is_continuous (λ (θ₀ : T tgt.2), op^.pdf (env.get_ks parents (env.insert tgt θ₀ inputs)) y) (env.get tgt inputs), from
assume (y : T ref.2),
begin
apply (T.continuous_multiple_args parents [] tgt inputs (λ xs, op^.pdf xs y) (env.get tgt inputs)),
intros idx H_at_idx,
dsimp,
apply (pdf_continuous H_at_idx H_wf^.m_contains_tgt H_gs_exist)
end,

have H_rest_continuous : ∀ (x : dvec T [ref.2]),
  T.is_continuous (λ (θ₀ : T tgt.2),
                    E (graph.to_dist (λ (m : env), ⟦sum_costs m costs⟧)
                                     (env.insert ref x^.head (env.insert tgt θ₀ inputs))
                                     nodes)
                      dvec.head)
                 (env.get tgt inputs), from
  assume x,
  have H_can_insert_x : ∀ (x : T ref.2), env.get tgt (env.insert ref x inputs) = env.get tgt inputs,
    begin intro y, dsimp, rw (env.get_insert_diff _ _ H_tgt_neq_ref) end,
  begin
    dsimp,
    simp [λ θ₀, env.insert_insert_flip x^.head θ₀ inputs (ne.symm H_tgt_neq_ref)],
    simp [eq.symm (H_can_insert_x x^.head)],
    exact (continuous_of_grads_exist (H_wfs _)^.left (H_gs_exist^.right _))
   end,

begin
dunfold graph.to_dist operator.to_dist,
simp [E.E_bind],
apply (E.E_continuous op (λ θ₀, env.get_ks parents (env.insert tgt θ₀ inputs)) _ _ H_pdf_continuous H_rest_continuous)
end

lemma rest_continuous {costs : list ID} {n : node} {nodes : list node} {inputs : env} {tgt : reference} {x : T n^.ref.2} :
  ∀ (x : dvec T [n^.ref.2]), tgt ≠ n^.ref →
  well_formed_at costs nodes (env.insert n^.ref x^.head inputs) tgt → grads_exist_at nodes (env.insert n^.ref x^.head inputs) tgt →
  T.is_continuous (λ (θ₀ : T tgt.2),
                    E (graph.to_dist (λ (m : env), ⟦sum_costs m costs⟧)
                                     (env.insert n^.ref x^.head (env.insert tgt θ₀ inputs))
                                     nodes)
                      dvec.head)
                 (env.get tgt inputs) :=
assume x H_tgt_neq_ref H_wf_tgt H_gs_exist_tgt,
have H_can_insert_x : ∀ (x : T n^.ref.2), env.get tgt (env.insert n^.ref x inputs) = env.get tgt inputs,
  begin intro y, dsimp, rw (env.get_insert_diff _ _ H_tgt_neq_ref) end,
begin
  dsimp,
  simp [λ θ₀, env.insert_insert_flip x^.head θ₀ inputs (ne.symm H_tgt_neq_ref)],
  simp [eq.symm (H_can_insert_x x^.head)],
  exact (continuous_of_grads_exist H_wf_tgt H_gs_exist_tgt)
end

private lemma fref_notin_parents :
  Π {n : node} {nodes : list node} {inputs : env} {fref : reference},
    all_parents_in_env inputs (n::nodes) →
    (¬ env.has_key fref inputs) →
    fref ∉ n^.parents :=
begin
intro n,
cases n with ref parents op,
dsimp,
intros nodes inputs fref H_ps_in_env H_fref_fresh H_fref_in_ps,
dunfold all_parents_in_env at H_ps_in_env,
exact H_fref_fresh (H_ps_in_env^.left fref H_fref_in_ps)
end

private lemma fref_neq_ref :
  Π {n : node} {nodes : list node} {inputs : env} {fref : reference},
    (¬ env.has_key fref inputs) → fref ∉ map node.ref (n::nodes) →
    fref ≠ n^.ref :=
begin
intros n nodes inputs fref H_fref_fresh₁ H_fref_fresh₂,
intro H_contra,
subst H_contra,
exact (ne_of_not_mem_cons H_fref_fresh₂) rfl
end

lemma to_dist_congr_insert :
  Π {costs : list ID} {nodes : list node} {inputs : env} {fref : reference} {fval : T fref.2},
    all_parents_in_env inputs nodes →
    (¬ env.has_key fref inputs) → fref ∉ map node.ref nodes →
    fref.1 ∉ costs →
E (graph.to_dist (λ env₀, ⟦sum_costs env₀ costs⟧) (env.insert fref fval inputs) nodes) dvec.head
=
E (graph.to_dist (λ env₀, ⟦sum_costs env₀ costs⟧) inputs nodes) dvec.head

| costs [] inputs fref fval H_ps_in_env H_fresh₁ H_fresh₂ H_not_cost :=
begin
dunfold graph.to_dist, simp [E.E_ret],
dunfold dvec.head sum_costs map,
induction costs with cost costs IH_cost,
-- case 1
reflexivity,
-- case 2
dunfold map sumr,

assertv H_neq : (cost, []) ≠ fref :=
begin
intro H_contra,
cases fref with fid fshape,
injection H_contra with H_cost H_ignore,
dsimp at H_not_cost,
rw H_cost at H_not_cost,
exact (ne_of_not_mem_cons H_not_cost rfl)
end,

assertv H_notin : fref.1 ∉ costs := not_mem_of_not_mem_cons H_not_cost,
simp [env.get_insert_diff fval inputs H_neq],
rw IH_cost H_notin
end

| costs (⟨ref, parents, operator.det op⟩::nodes) inputs fref fval H_ps_in_env H_fresh₁ H_fresh₂ H_not_cost :=
begin
dunfold graph.to_dist operator.to_dist,
simp [E.E_bind, E.E_ret],
assertv H_fref_notin_parents : fref ∉ parents := fref_notin_parents H_ps_in_env H_fresh₁,
assertv H_fref_neq_ref : fref ≠ ref := fref_neq_ref H_fresh₁ H_fresh₂,
rw env.get_ks_insert_diff H_fref_notin_parents,
rw env.insert_insert_flip _ _ _ (ne.symm H_fref_neq_ref),
dsimp,
apply (to_dist_congr_insert (H_ps_in_env^.right _) _ _ H_not_cost),
{ intro H_contra, exact H_fresh₁ (env.has_key_insert_diff H_fref_neq_ref H_contra) },
{ exact not_mem_of_not_mem_cons H_fresh₂ }
end

| costs (⟨ref, parents, operator.rand op⟩::nodes) inputs fref fval H_ps_in_env H_fresh₁ H_fresh₂ H_not_cost :=
begin
dunfold graph.to_dist operator.to_dist,
simp [E.E_bind, E.E_ret],
assertv H_fref_notin_parents : fref ∉ parents := fref_notin_parents H_ps_in_env H_fresh₁,
assertv H_fref_neq_ref : fref ≠ ref := fref_neq_ref H_fresh₁ H_fresh₂,
rw env.get_ks_insert_diff H_fref_notin_parents,

apply congr_arg,
apply funext,
intro x,

rw env.insert_insert_flip _ _ _ (ne.symm H_fref_neq_ref),
apply (to_dist_congr_insert (H_ps_in_env^.right _) _ _ H_not_cost),
{ intro H_contra, exact H_fresh₁ (env.has_key_insert_diff H_fref_neq_ref H_contra) },
{ exact not_mem_of_not_mem_cons H_fresh₂ }
end

lemma map_filter_expand_helper {costs : list ID} (ref : reference) (parents : list reference)
                               (op : rand.op parents^.p2 ref.2)
                               (nodes : list node) (inputs : env) (tgt : reference) :
well_formed_at costs (⟨ref, parents, operator.rand op⟩::nodes) inputs tgt →
grads_exist_at (⟨ref, parents, operator.rand op⟩::nodes) inputs tgt →

∀ (y : T ref.2),
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
    (filter (λ (idx : ℕ), tgt = dnth parents idx) (riota (length parents))) = map
    (λ (x : ℕ),
       E
         (graph.to_dist
            (λ (m : env),
               ⟦(λ (m : env) (idx : ℕ),
                  sum_downstream_costs nodes costs ref m ⬝ rand.op.glogpdf op (env.get_ks parents m) (env.get ref m)
                    idx
                    (tgt.snd))
                 m
                 x⟧)
            ((λ (y : T (ref.snd)), env.insert ref y inputs) y)
            nodes)
         dvec.head)
    (filter (λ (idx : ℕ), tgt = dnth parents idx) (riota (length parents))) :=
assume H_wf H_gs_exist y,
let θ := env.get tgt inputs in
let next_inputs := λ (y : T ref.2), env.insert ref y inputs in

have H_ref_in_refs : ref ∈ ref :: map node.ref nodes, from mem_of_cons_same,
have H_ref_notin_parents : ref ∉ parents, from ref_notin_parents H_wf^.ps_in_env H_wf^.uids,

have H_get_ks_next_inputs : env.get_ks parents (next_inputs y) = env.get_ks parents inputs,
  begin dsimp, rw (env.get_ks_insert_diff H_ref_notin_parents) end,

have H_wfs : ∀ y, well_formed_at costs nodes (next_inputs y) tgt ∧ well_formed_at costs nodes (next_inputs y) ref,
  from assume y, wf_at_next H_wf,

begin

-- Apply map_filter_congr
apply map_filter_congr,
intros idx H_idx_in_riota H_tgt_dnth_parents_idx,
assertv H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_dnth_parents_idx⟩,
assertv H_tshape_at_idx : at_idx parents^.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx,
assertv H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx,

-- 7. Replace `m` with `inputs`/`next_inputs` so that we can use the gradient rule for the logpdf
dunfold sum_downstream_costs,

assert H_swap_m_for_inputs :
(graph.to_dist
       (λ (m : env),
          ⟦sum_costs m costs ⬝ rand.op.glogpdf op (env.get_ks parents m) (env.get ref m) idx (tgt^.snd)⟧)
       (env.insert ref y inputs)
       nodes)
=
(graph.to_dist
       (λ (m : env),
          ⟦sum_costs m costs ⬝ rand.op.glogpdf op (env.get_ks parents (next_inputs y)) (env.get ref (next_inputs y)) idx (tgt^.snd)⟧)
       (env.insert ref y inputs)
       nodes),
begin
  apply graph.to_dist_congr,
  exact (H_wfs y)^.left^.uids,
  dsimp,
  intros m H_envs_match,
  apply dvec.singleton_congr,
  assert H_parents_match : env.get_ks parents m = env.get_ks parents (next_inputs y),
  begin
    apply env.get_ks_env_eq,
    intros parent H_parent_in_parents,
    apply H_envs_match,
    apply env.has_key_insert,
    exact (H_wf^.ps_in_env^.left parent H_parent_in_parents)
  end,
  assert H_ref_matches : env.get ref m = y,
  begin
    assertv H_env.has_key_ref : env.has_key ref (next_inputs y) := env.has_key_insert_same _ _,
    rw [H_envs_match ref H_env.has_key_ref, env.get_insert_same]
  end,
  simp [H_parents_match, H_ref_matches, env.get_insert_same],
end,

erw H_swap_m_for_inputs,
clear H_swap_m_for_inputs,

-- 8. push E over ⬝ and cancel the first terms
rw E.E_k_scale,
apply congr_arg,

-- 9. Use glogpdf correct
assertv H_glogpdf_pre : op^.pre (env.get_ks parents (next_inputs y)) :=
  begin dsimp, rw (env.get_ks_insert_diff H_ref_notin_parents), exact (H_gs_exist^.left H_tgt_in_parents) end,

rw (op^.glogpdf_correct H_tshape_at_idx H_glogpdf_pre),

-- 10. Clean-up
dunfold E dvec.head,
dsimp,
simp [H_get_ks_next_inputs, env.get_insert_same],
rw (env.dvec_get_get_ks inputs H_tgt_at_idx)
end

lemma sum_costs_differentiable : Π (costs : list ID) (tgt : reference) (inputs : env),
  T.is_cdifferentiable (λ (θ₀ : T (tgt.snd)), sumr (map (λ (cost : ID), env.get (cost, @nil ℕ) (env.insert tgt θ₀ inputs)) costs))
                      (env.get tgt inputs) :=
begin
intros costs tgt inputs,
induction costs with cost costs IHcosts,
{ dunfold sumr map, apply T.is_cdifferentiable_const },
{
dunfold sumr map, apply iff.mp (T.is_cdifferentiable_add_fs _ _ _),
split,
tactic.swap,
exact IHcosts,
assertv H_em : tgt = (cost, []) ∨ tgt ≠ (cost, []) := decidable.em _, cases H_em with H_eq H_neq,
-- case 1: tgt = (cost, [])
{ rw H_eq, simp only [env.get_insert_same], apply T.is_cdifferentiable_id },
-- case 2: tgt ≠ (cost, [])
{ simp only [λ (x : T tgt.2), env.get_insert_diff x inputs (ne.symm H_neq), H_neq], apply T.is_cdifferentiable_const }
}
end



end certigrad
