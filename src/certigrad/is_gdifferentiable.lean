import .graph .predicates .lemmas

namespace certigrad
open list

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
have H_tgt_in_keys : tgt ∈ env.keys inputs, from env.has_key_mem_keys H_wf^.m_contains_tgt,
have H_ref_in_refs : ref ∈ ref :: map node.ref nodes, from mem_of_cons_same,

have H_ref_notin_parents : ref ∉ parents, from ref_notin_parents H_wf^.ps_in_env H_wf^.nodup,

have H_tgt_neq_ref : tgt ≠ ref, from nodup_append_neq H_tgt_in_keys H_ref_in_refs H_wf^.nodup,

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
dsimp [dvec.head],
simp only [env.insert_get_same],
simp only [H_can_insert] at H_pdiff_tgt,
exact H_pdiff_tgt
}, -- end case 1, simple recursive case

-- start case 2
dsimp,
simp only [λ (x : T ref.2) (θ : T tgt.2), env.insert_insert_flip x θ inputs (ne.symm H_tgt_neq_ref)],
dsimp [dvec.head],

apply T.is_cdifferentiable_multiple_args _ _ _ op^.f _ (λ (x' : T ref.snd),
       E
         (graph.to_dist
            (λ (m : dmap (ID × list ℕ) (λ (ref : ID × list ℕ), T (ref.snd))), ⟦sum_costs m costs⟧)
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
simp only [env.insert_get_same],

note H_odiff := op^.is_odiff (env.get_ks parents inputs) (H_gs_exist^.right H_tgt_in_parents)^.left idx tgt.2 H_tshape_at_idx
                   (λ x', E (graph.to_dist (λ (m : env), ⟦sum_costs m costs⟧)
                                           (env.insert tgt (env.get tgt inputs) (env.insert ref x' inputs))
                                            nodes)
                             dvec.head),

simp only [λ m, env.dvec_get_get_ks m H_tgt_at_idx] at H_odiff,
apply H_odiff,

dsimp at H_pdiff_ref,
simp only [env.get_insert_same] at H_pdiff_ref,

simp only [λ (x : T ref.2) (θ : T tgt.2), env.insert_insert_flip θ x inputs H_tgt_neq_ref, env.insert_get_same],
simp only [env.insert_insert_same] at H_pdiff_ref,
exact H_pdiff_ref
end

| tgt inputs (⟨ref, parents, operator.rand op⟩ :: nodes) :=
assume H_wf H_gs_exist H_pdfs_exist H_diff_under_int,

let θ := env.get tgt inputs in
let next_inputs := λ (y : T ref.2), env.insert ref y inputs in

-- 0. Collect useful helpers
have H_tgt_in_keys : tgt ∈ env.keys inputs, from env.has_key_mem_keys H_wf^.m_contains_tgt,
have H_ref_in_refs : ref ∈ ref :: map node.ref nodes, from mem_of_cons_same,
have H_ref_notin_parents : ref ∉ parents, from ref_notin_parents H_wf^.ps_in_env H_wf^.nodup,
have H_tgt_neq_ref : tgt ≠ ref, from nodup_append_neq H_tgt_in_keys H_ref_in_refs H_wf^.nodup,
have H_insert_θ : env.insert tgt θ inputs = inputs, by rw env.insert_get_same,

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
            (λ (m : dmap (ID × list ℕ) (λ (ref : ID × list ℕ), T (ref.snd))), ⟦sum_costs m costs⟧)
            (env.insert ref x (env.insert tgt θ₀ inputs))
            nodes)
         dvec.head)
    (env.get tgt inputs), from H_diff_under_int^.left^.left^.left,

have H_g_grad_uint : T.is_uniformly_integrable_around
    (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)),
       ∇
         (λ (θ₁ : T (tgt.snd)),
            (λ (x : T (ref.snd)) (θ₀ : T (tgt.snd)),
               rand.op.pdf op (env.get_ks parents (env.insert tgt θ₀ inputs)) x ⬝ E
                 (graph.to_dist
                    (λ (m : dmap (ID × list ℕ) (λ (ref : ID × list ℕ), T (ref.snd))), ⟦sum_costs m costs⟧)
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
simp only [env.insert_get_same],
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

have H_tgt_in_keys : tgt ∈ env.keys inputs, from env.has_key_mem_keys H_wf^.m_contains_tgt,
have H_ref_in_refs : ref ∈ ref :: map node.ref nodes, from mem_of_cons_same,

have H_ref_notin_parents : ref ∉ parents, from ref_notin_parents H_wf^.ps_in_env H_wf^.nodup,

have H_tgt_neq_ref : tgt ≠ ref, from nodup_append_neq H_tgt_in_keys H_ref_in_refs H_wf^.nodup,

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
simp only [env.insert_get_same, env.get_insert_same],
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
simp only [env.insert_get_same],
simp only [env.get_insert_same, env.insert_insert_same] at H_pdiff,

note H_odiff := op^.is_odiff (env.get_ks parents inputs) (H_gs_exist^.right H_tgt_in_parents)^.left idx tgt.2 H_tshape_at_idx
                   (λ x', E (graph.to_dist (λ (m : env), ⟦sum_costs m costs⟧)
                                           (env.insert tgt (env.get tgt inputs) (env.insert ref x' inputs))
                                            nodes)
                             dvec.head),

simp only [λ m, env.dvec_get_get_ks m H_tgt_at_idx] at H_odiff,
simp only [λ (x : T ref.2) (θ : T tgt.2), env.insert_insert_flip θ x inputs H_tgt_neq_ref, env.insert_get_same] at H_odiff,
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
dsimp,
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
have H_tgt_in_keys : tgt ∈ env.keys inputs, from env.has_key_mem_keys H_wf^.m_contains_tgt,
have H_ref_in_refs : ref ∈ ref :: map node.ref nodes, from mem_of_cons_same,
have H_ref_notin_parents : ref ∉ parents, from ref_notin_parents H_wf^.ps_in_env H_wf^.nodup,
have H_tgt_neq_ref : tgt ≠ ref, from nodup_append_neq H_tgt_in_keys H_ref_in_refs H_wf^.nodup,
have H_insert_θ : env.insert tgt θ inputs = inputs, by rw env.insert_get_same,

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

note H_g_uint := H_diff_under_int^.left^.left^.right,
note H_g_grad_uint := H_diff_under_int^.left^.right^.left^.right,
apply T.is_cdifferentiable_integral _ _ _ H_g_uint H_g_grad_uint,

intro y,
apply iff.mp (T.is_cdifferentiable_scale_f _ _ _),

note H_pdiff := pd_is_cdifferentiable costs tgt (next_inputs y) nodes (H_wfs y)^.left (H_gs_exist^.right y) (H_pdfs_exist^.right y) (H_diff_under_int^.right y),
dsimp [dvec.head], dsimp at H_pdiff,
simp only [H_can_insert_y] at H_pdiff,
simp only [λ (x : T ref.2) (θ : T tgt.2), env.insert_insert_flip θ x inputs H_tgt_neq_ref, env.insert_get_same] at H_pdiff,
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
dsimp [dvec.head],

note H_pdf_cdiff := @rand.op.pdf_cdiff _ _ op (env.get_ks parents inputs) y idx tgt.2 H_tshape_at_idx H_pdfs_exist^.left,
dsimp [rand.pdf_cdiff] at H_pdf_cdiff,
simp only [env.insert_get_same],
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

end certigrad
