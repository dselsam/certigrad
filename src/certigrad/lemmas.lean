/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Miscellaneous lemmas.
-/
import .predicates .tcont .expected_value

namespace certigrad
open list

lemma env_not_has_key_insert {m : env} {ref₁ ref₂ : reference} {x : T ref₂.2} :
  ref₁ ≠ ref₂ → (¬ env.has_key ref₁ m) → (¬ env.has_key ref₁ (env.insert ref₂ x m)) :=
begin
intros H_neq H_nin H_in,
exact H_nin (env.has_key_insert_diff H_neq H_in)
end

lemma env_in_nin_ne {m : env} {ref₁ ref₂ : reference} : env.has_key ref₁ m → (¬ env.has_key ref₂ m) → ref₁ ≠ ref₂ :=
begin
intros H_in H_nin H_eq,
subst H_eq,
exact H_nin H_in
end

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
intros H_tgt H_uids,
exact env_in_nin_ne H_tgt H_uids^.left
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

lemma can_diff_under_ints_alt1 {costs : list ID}
  {ref : reference} {parents : list reference} {op : rand.op parents^.p2 ref.2} {nodes : list node} {inputs : env} {tgt : reference} :
  let θ : T tgt.2 := env.get tgt inputs in
  let g : T ref.2 → T tgt.2 → ℝ :=
  (λ (x : T ref.2) (θ₀ : T tgt.2),
      E (graph.to_dist (λ (inputs : env), ⟦sum_costs inputs costs⟧)
                       (env.insert ref x (env.insert tgt θ₀ inputs))
                       nodes)
        dvec.head) in
  let next_inputs := (λ (y : T ref.2), env.insert ref y inputs) in

can_differentiate_under_integrals costs (⟨ref, parents, operator.rand op⟩ :: nodes) inputs tgt
→
T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)), rand.op.pdf op (env.get_ks parents (env.insert tgt θ inputs)) x ⬝ g x θ₀) θ :=
begin
dsimp [can_differentiate_under_integrals],
intro H_cdi,
note H := H_cdi^.left^.left,
clear H_cdi,
apply T.uint_right (λ θ₁ θ₂ x,
rand.op.pdf op (env.get_ks parents (env.insert tgt θ₁ inputs)) x ⬝
         E
           (graph.to_dist (λ (inputs : env), ⟦sum_costs inputs costs⟧)
              (env.insert ref x (env.insert tgt θ₂ inputs))
              nodes)
           dvec.head) _ H
end

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
apply (op^.is_ocont (env.get_ks parents inputs) (at_idx_p2 H_at_idx) (H_gs_exist^.right $ mem_of_at_idx H_at_idx)^.left),
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
            (λ (m : env), ⟦sum_costs m costs⟧)
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

lemma pd_is_cdifferentiable (costs : list ID) : Π (tgt : reference) (inputs : env) (nodes : list node),
  well_formed_at costs nodes inputs tgt →
  grads_exist_at nodes inputs tgt →
  pdfs_exist_at nodes inputs →
  can_differentiate_under_integrals costs nodes inputs tgt →

  T.is_cdifferentiable (λ (θ₀ : T tgt.2), E (graph.to_dist (λ m, ⟦sum_costs m costs⟧) (env.insert tgt θ₀ inputs) nodes) dvec.head) (env.get tgt inputs)
| tgt inputs [] := assume H_wf H_gs_exist H_pdfs_exist H_diff_under_int, sum_costs_differentiable costs tgt inputs

| tgt inputs (⟨ref, parents, operator.det op⟩ :: nodes) :=
assume H_wf H_gs_exist H_pdfs_exist H_diff_under_int,

let θ := env.get tgt inputs in
let x := op^.f (env.get_ks parents inputs) in
let next_inputs := env.insert ref x inputs in

-- 0. Collect useful helpers
have H_ref_in_refs : ref ∈ ref :: map node.ref nodes, from mem_of_cons_same,

have H_ref_notin_parents : ref ∉ parents, from ref_notin_parents H_wf^.ps_in_env H_wf^.uids,

have H_tgt_neq_ref : tgt ≠ ref, from ref_ne_tgt H_wf^.m_contains_tgt H_wf^.uids,

have H_can_insert : env.get tgt next_inputs = env.get tgt inputs,
  begin dsimp, rw (env.get_insert_diff _ _ H_tgt_neq_ref) end,

have H_wfs : well_formed_at costs nodes next_inputs tgt ∧ well_formed_at costs nodes next_inputs ref, from wf_at_next H_wf,
have H_gs_exist_tgt : grads_exist_at nodes next_inputs tgt, from H_gs_exist^.left,
have H_pdfs_exist_next : pdfs_exist_at nodes next_inputs, from H_pdfs_exist,

begin
note H_pdiff_tgt := pd_is_cdifferentiable tgt next_inputs nodes H_wfs^.left H_gs_exist_tgt H_pdfs_exist_next H_diff_under_int^.left,

dsimp [graph.to_dist, operator.to_dist],
simp only [E.E_ret, E.E_bind, dvec.head],
apply T.is_cdifferentiable_binary (λ θ₁ θ₂, E (graph.to_dist (λ (m : env), ⟦sum_costs m costs⟧)
                                                            (env.insert ref (det.op.f op (env.get_ks parents (env.insert tgt θ₂ inputs))) (env.insert tgt θ₁ inputs))
                                                            nodes)
                                             dvec.head),
{ -- case 1, simple recursive case
dsimp,
simp only [λ (x : T ref.2) (θ : T tgt.2), env.insert_insert_flip x θ inputs (ne.symm H_tgt_neq_ref)],
simp only [env.insert_get_same H_wf^.m_contains_tgt],
simp only [H_can_insert] at H_pdiff_tgt,
exact H_pdiff_tgt
}, -- end case 1, simple recursive case

-- start case 2
dsimp,
simp only [λ (x : T ref.2) (θ : T tgt.2), env.insert_insert_flip x θ inputs (ne.symm H_tgt_neq_ref)],

apply T.is_cdifferentiable_multiple_args _ _ _ op^.f _ (λ (x' : T ref.snd),
       E
         (graph.to_dist
            (λ (m : env), ⟦sum_costs m costs⟧)
            (env.insert tgt (env.get tgt inputs) (env.insert ref x' inputs))
            nodes)
         dvec.head),

intros idx H_idx_in_riota H_tgt_eq_dnth_idx,
assertv H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_eq_dnth_idx⟩,
assertv H_tshape_at_idx : at_idx parents^.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx,
assertv H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx,

dsimp,

assertv H_gs_exist_ref : grads_exist_at nodes next_inputs ref := (H_gs_exist^.right H_tgt_in_parents)^.right,
assertv H_diff_under_int_ref : can_differentiate_under_integrals costs nodes next_inputs ref := H_diff_under_int^.right H_tgt_in_parents,

note H_pdiff_ref := pd_is_cdifferentiable ref next_inputs nodes H_wfs^.right H_gs_exist_ref H_pdfs_exist_next H_diff_under_int_ref,
simp only [env.insert_get_same H_wf^.m_contains_tgt],

note H_odiff := op^.is_odiff (env.get_ks parents inputs) (H_gs_exist^.right H_tgt_in_parents)^.left idx tgt.2 H_tshape_at_idx
                   (λ x', E (graph.to_dist (λ (m : env), ⟦sum_costs m costs⟧)
                                           (env.insert tgt (env.get tgt inputs) (env.insert ref x' inputs))
                                            nodes)
                             dvec.head),

simp only [λ m, env.dvec_get_get_ks m H_tgt_at_idx] at H_odiff,
apply H_odiff,

dsimp at H_pdiff_ref,
simp only [env.get_insert_same] at H_pdiff_ref,

simp only [λ (x : T ref.2) (θ : T tgt.2), env.insert_insert_flip θ x inputs H_tgt_neq_ref, env.insert_get_same H_wf^.m_contains_tgt],
simp only [env.insert_insert_same] at H_pdiff_ref,
exact H_pdiff_ref
end

| tgt inputs (⟨ref, parents, operator.rand op⟩ :: nodes) :=
assume H_wf H_gs_exist H_pdfs_exist H_diff_under_int,

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

let g : T ref.2 → T tgt.2 → ℝ :=
  (λ (x : T ref.2) (θ₀ : T tgt.2),
      E (graph.to_dist (λ (m : env), ⟦sum_costs m costs⟧)
                       (env.insert ref x (env.insert tgt θ₀ inputs))
                       nodes)
        dvec.head) in

have H_g_uint : T.is_uniformly_integrable_around
    (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)),
       rand.op.pdf op (env.get_ks parents (env.insert tgt θ₀ inputs)) x ⬝ E
         (graph.to_dist
            (λ (m : env), ⟦sum_costs m costs⟧)
            (env.insert ref x (env.insert tgt θ₀ inputs))
            nodes)
         dvec.head)
    (env.get tgt inputs), from H_diff_under_int^.left^.left,

have H_g_grad_uint : T.is_uniformly_integrable_around
    (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)),
       ∇
         (λ (θ₁ : T (tgt.snd)),
            (λ (x : T (ref.snd)) (θ₀ : T (tgt.snd)),
               rand.op.pdf op (env.get_ks parents (env.insert tgt θ₀ inputs)) x ⬝ E
                 (graph.to_dist
                    (λ (m : env), ⟦sum_costs m costs⟧)
                    (env.insert ref x (env.insert tgt θ₀ inputs))
                    nodes)
                 dvec.head)
              x
              θ₁)
         θ₀)
    (env.get tgt inputs), from H_diff_under_int^.left^.right^.left^.left,

begin
dunfold graph.to_dist operator.to_dist,
simp only [E.E_bind],

note H_pdiff_tgt := λ y, pd_is_cdifferentiable tgt (next_inputs y) nodes (H_wfs y)^.left (H_gs_exist^.right y) (H_pdfs_exist^.right y) (H_diff_under_int^.right y),
dunfold E T.dintegral dvec.head,
apply T.is_cdifferentiable_integral _ _ _ H_g_uint H_g_grad_uint,

intro y,

apply T.is_cdifferentiable_binary (λ θ₁ θ₂, rand.op.pdf op (env.get_ks parents (env.insert tgt θ₁ inputs)) y
                                           ⬝ E (graph.to_dist (λ (m : env), ⟦sum_costs m costs⟧) (env.insert ref y (env.insert tgt θ₂ inputs)) nodes) dvec.head),
begin -- start PDF differentiable
dsimp,
apply iff.mp (T.is_cdifferentiable_fscale _ _ _),
apply T.is_cdifferentiable_multiple_args _ _ _ (λ θ, op^.pdf θ y) _ (λ y : ℝ, y),
intros idx H_idx_in_riota H_tgt_eq_dnth_idx,
assertv H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_eq_dnth_idx⟩,
assertv H_tshape_at_idx : at_idx parents^.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx,
assertv H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx,
dsimp,

note H_pdf_cdiff := @rand.op.pdf_cdiff _ _ op (env.get_ks parents inputs) y idx tgt.2 H_tshape_at_idx H_pdfs_exist^.left,
dsimp [rand.pdf_cdiff] at H_pdf_cdiff,
simp only [env.insert_get_same H_wf^.m_contains_tgt],
simp only [λ m, env.dvec_get_get_ks m H_tgt_at_idx] at H_pdf_cdiff,
exact H_pdf_cdiff,
end, -- end PDF differentiable

begin -- start E differentiable
dsimp,
dsimp at H_pdiff_tgt,
apply iff.mp (T.is_cdifferentiable_scale_f _ _ _),
simp only [λ x y z, env.insert_insert_flip x y z H_tgt_neq_ref] at H_pdiff_tgt,
simp only [λ x y, env.get_insert_diff x y H_tgt_neq_ref] at H_pdiff_tgt,
apply H_pdiff_tgt
end -- end E differentiable

end

lemma is_gdifferentiable_of_pre {costs : list ID} : Π (tgt : reference) (inputs : env) (nodes : list node),
  well_formed_at costs nodes inputs tgt →
  grads_exist_at nodes inputs tgt →
  pdfs_exist_at nodes inputs →
  can_differentiate_under_integrals costs nodes inputs tgt →
  is_gdifferentiable (λ m, ⟦sum_costs m costs⟧) tgt inputs nodes dvec.head
| tgt inputs [] := λ H_wf H_gs_exist H_pdfs_exist H_diff_under_int, trivial

| tgt inputs (⟨ref, parents, operator.det op⟩ :: nodes) :=
assume H_wf H_gs_exist H_pdfs_exist H_diff_under_int,

let θ := env.get tgt inputs in
let x := op^.f (env.get_ks parents inputs) in
let next_inputs := env.insert ref x inputs in

have H_ref_in_refs : ref ∈ ref :: map node.ref nodes, from mem_of_cons_same,

have H_ref_notin_parents : ref ∉ parents, from ref_notin_parents H_wf^.ps_in_env H_wf^.uids,

have H_tgt_neq_ref : tgt ≠ ref, from ref_ne_tgt H_wf^.m_contains_tgt H_wf^.uids,

have H_can_insert : env.get tgt next_inputs = env.get tgt inputs,
  begin dsimp, rw (env.get_insert_diff _ _ H_tgt_neq_ref) end,

have H_wfs : well_formed_at costs nodes next_inputs tgt ∧ well_formed_at costs nodes next_inputs ref, from wf_at_next H_wf,

have H_gs_exist_tgt : grads_exist_at nodes next_inputs tgt, from H_gs_exist^.left,
have H_pdfs_exist_next : pdfs_exist_at nodes next_inputs, from H_pdfs_exist,

have H_gdiff_tgt : is_gdifferentiable (λ m, ⟦sum_costs m costs⟧) tgt next_inputs nodes dvec.head, from
  is_gdifferentiable_of_pre tgt next_inputs nodes H_wfs^.left H_gs_exist_tgt H_pdfs_exist_next H_diff_under_int^.left,

begin
dsimp [grads_exist_at] at H_gs_exist,
dsimp [pdfs_exist_at] at H_pdfs_exist,
dsimp [is_gdifferentiable] at H_gdiff_tgt,
dsimp [is_gdifferentiable],
-- TODO(dhs): replace once `apply` tactic can handle nesting
split, tactic.rotate 1, split, tactic.rotate 1, split, tactic.rotate 2,

----------------------------------- start 1/4
begin
simp only [env.insert_get_same H_wf^.m_contains_tgt, env.get_insert_same],
note H_pdiff := pd_is_cdifferentiable costs tgt next_inputs nodes H_wfs^.left H_gs_exist_tgt H_pdfs_exist_next H_diff_under_int^.left,
dsimp at H_pdiff,
simp only [H_can_insert] at H_pdiff,
simp only [λ (x : T ref.2) (θ : T tgt.2), env.insert_insert_flip θ x inputs H_tgt_neq_ref] at H_pdiff,
exact H_pdiff,
end,
----------------------------------- end 1/4

----------------------------------- start 2/4
begin
apply T.is_cdifferentiable_sumr,
intros idx H_idx_in_filter,
cases of_in_filter _ _ _ H_idx_in_filter with H_idx_in_riota H_tgt_eq_dnth_idx,
assertv H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_eq_dnth_idx⟩,
assertv H_tshape_at_idx : at_idx parents^.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx,
assertv H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx,
assertv H_gs_exist_ref : grads_exist_at nodes next_inputs ref := (H_gs_exist^.right H_tgt_in_parents)^.right,

note H_pdiff := pd_is_cdifferentiable costs ref next_inputs nodes H_wfs^.right H_gs_exist_ref H_pdfs_exist_next (H_diff_under_int^.right H_tgt_in_parents),
dsimp at H_pdiff,
simp only [env.insert_get_same H_wf^.m_contains_tgt],
simp only [env.get_insert_same, env.insert_insert_same] at H_pdiff,

note H_odiff := op^.is_odiff (env.get_ks parents inputs) (H_gs_exist^.right H_tgt_in_parents)^.left idx tgt.2 H_tshape_at_idx
                   (λ x', E (graph.to_dist (λ (m : env), ⟦sum_costs m costs⟧)
                                           (env.insert tgt (env.get tgt inputs) (env.insert ref x' inputs))
                                            nodes)
                             dvec.head),

simp only [λ m, env.dvec_get_get_ks m H_tgt_at_idx] at H_odiff,
simp only [λ (x : T ref.2) (θ : T tgt.2), env.insert_insert_flip θ x inputs H_tgt_neq_ref, env.insert_get_same H_wf^.m_contains_tgt] at H_odiff,
apply H_odiff,
exact H_pdiff
end,
----------------------------------- end 2/4

----------------------------------- start 3/4
begin
exact H_gdiff_tgt
end,
----------------------------------- end 3/4

----------------------------------- start 4/4
begin
intros idx H_idx_in_riota H_tgt_eq_dnth_idx,
assertv H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_eq_dnth_idx⟩,
assertv H_tshape_at_idx : at_idx parents^.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx,
assertv H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx,
assertv H_gs_exist_ref : grads_exist_at nodes next_inputs ref := (H_gs_exist^.right H_tgt_in_parents)^.right,
apply is_gdifferentiable_of_pre ref next_inputs nodes H_wfs^.right H_gs_exist_ref H_pdfs_exist_next (H_diff_under_int^.right H_tgt_in_parents),
end,
----------------------------------- end 4/4

end

| tgt inputs (⟨ref, parents, operator.rand op⟩ :: nodes) :=
assume H_wf H_gs_exist H_pdfs_exist H_diff_under_int,
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
dsimp [is_gdifferentiable],
-- TODO(dhs): use apply and.intro _ (and.intro _ _) once tactic is fixed
split, tactic.rotate 1, split, tactic.rotate 2,

----------------------------------- start 1/3
begin
dunfold E T.dintegral,

note H_g_uint := can_diff_under_ints_alt1 H_diff_under_int,
note H_g_grad_uint := H_diff_under_int^.left^.right^.left^.right,
apply T.is_cdifferentiable_integral _ _ _ H_g_uint H_g_grad_uint,

intro y,
apply iff.mp (T.is_cdifferentiable_scale_f _ _ _),

note H_pdiff := pd_is_cdifferentiable costs tgt (next_inputs y) nodes (H_wfs y)^.left (H_gs_exist^.right y) (H_pdfs_exist^.right y) (H_diff_under_int^.right y),
dsimp [dvec.head], dsimp at H_pdiff,
simp only [H_can_insert_y] at H_pdiff,
simp only [λ (x : T ref.2) (θ : T tgt.2), env.insert_insert_flip θ x inputs H_tgt_neq_ref, env.insert_get_same H_wf^.m_contains_tgt] at H_pdiff,
exact H_pdiff
end,
----------------------------------- end 1/3


----------------------------------- start 2/3
begin
apply T.is_cdifferentiable_sumr,
intros idx H_idx_in_filter,
cases of_in_filter _ _ _ H_idx_in_filter with H_idx_in_riota H_tgt_eq_dnth_idx,
assertv H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_eq_dnth_idx⟩,
assertv H_tshape_at_idx : at_idx parents^.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx,
assertv H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx,

note H_g_uint_idx := H_diff_under_int^.left^.right^.right^.left _ H_tgt_at_idx,
note H_g_grad_uint_idx := H_diff_under_int^.left^.right^.right^.right _ H_tgt_at_idx,

dunfold E T.dintegral,
apply T.is_cdifferentiable_integral _ _ _ H_g_uint_idx H_g_grad_uint_idx,
tactic.rotate 2,
dsimp [dvec.head],

intro y,
apply iff.mp (T.is_cdifferentiable_fscale _ _ _),

note H_pdf_cdiff := @rand.op.pdf_cdiff _ _ op (env.get_ks parents inputs) y idx tgt.2 H_tshape_at_idx H_pdfs_exist^.left,
dsimp [rand.pdf_cdiff] at H_pdf_cdiff,
simp only [env.insert_get_same H_wf^.m_contains_tgt],
simp only [λ m, env.dvec_get_get_ks m H_tgt_at_idx] at H_pdf_cdiff,
exact H_pdf_cdiff,
end,
----------------------------------- end 2/3

----------------------------------- start 3/3
begin
exact λ y, is_gdifferentiable_of_pre _ _ _ (H_wfs y)^.left (H_gs_exist^.right y) (H_pdfs_exist^.right y) (H_diff_under_int^.right y)
end
----------------------------------- end 3/3

end

lemma can_diff_under_ints_of_all_pdfs_std (costs : list ID) : Π (nodes : list node) (m : env) (tgt : reference),
  all_pdfs_std nodes
  → can_diff_under_ints_pdfs_std costs nodes m tgt
  → can_differentiate_under_integrals costs nodes m tgt
| [] m tgt H_std H_cdi := trivial

| (⟨ref, parents, operator.det op⟩ :: nodes) m tgt H_std H_cdi :=
begin
simp [all_pdfs_std_det] at H_std,
dsimp [can_diff_under_ints_pdfs_std] at H_cdi,
dsimp [can_differentiate_under_integrals],
split,
apply can_diff_under_ints_of_all_pdfs_std,
exact H_std,
exact H_cdi^.left,
intro H_in,
apply can_diff_under_ints_of_all_pdfs_std,
exact H_std,
exact H_cdi^.right H_in
end

| (⟨(ref, .(shape)), [], operator.rand (rand.op.mvn_iso_std shape)⟩ :: nodes) m tgt H_std H_cdi :=
begin
dsimp [all_pdfs_std] at H_std,
dsimp [can_diff_under_ints_pdfs_std] at H_cdi,
dsimp [can_differentiate_under_integrals],
split,
split,
exact H_cdi^.left^.left,
split,
exact H_cdi^.left^.right,
split,
intros H H_contra,
exfalso,
exact list.at_idx_over H_contra (nat.not_lt_zero _),
intros H H_contra,
exfalso,
exact list.at_idx_over H_contra (nat.not_lt_zero _),
intro y,
apply can_diff_under_ints_of_all_pdfs_std,
exact H_std,
exact H_cdi^.right y
end

| (⟨(ref, .(shape)), [(parent₁, .(shape)), (parent₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩ :: nodes) m tgt H_std H_cdi :=
begin
dsimp [all_pdfs_std] at H_std,
exfalso,
exact H_std
end

end certigrad
