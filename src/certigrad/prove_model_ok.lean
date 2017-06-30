/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Tactics to prove specific models satisfy the preconditions of backprop_correct.
-/
import data.list.set .tfacts .graph .predicates .expected_value .reparam .kl .tactics .program .mvn .tactics

#print "compiling prove_model_ok..."

namespace certigrad
open T tactic list

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
@[cgsimp] lemma and_false_left {P : Prop} : (false ∧ P) = false := propext (false_and _)
@[cgsimp] lemma and_false_right {P : Prop} : (P ∧ false) = false := propext (and_false _)

@[cgsimp] lemma or_false_left {P : Prop} : (false ∨ P) = P := propext (false_or _)
@[cgsimp] lemma or_false_right {P : Prop} : (P ∨ false) = P := propext (or_false _)
@[cgsimp] lemma or_true_left {P : Prop} : (true ∨ P) = true := propext (true_or _)
@[cgsimp] lemma or_true_right {P : Prop} : (P ∨ true) = true := propext (or_true _)

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

def is_not_used_downstream (tgt : reference) : list node → Prop
| [] := true
| (⟨ref, parents, op⟩ :: nodes) := tgt ∉ parents ∧ is_not_used_downstream nodes

def is_used_downstream (tgt : reference) : list node → Prop
| [] := false
| (⟨ref, parents, op⟩ :: nodes) := tgt ∈ parents ∨ is_used_downstream nodes

attribute [cgsimp] is_not_used_downstream is_used_downstream

lemma costs_helper : Π (costs : list ID) (tgt : reference) (m : env),
  tgt.1 ∉ costs → compute_grad_slow costs [] m tgt = 0
| []      tgt m H_nin := rfl
| (c::cs) tgt m H_nin :=
begin
dunfold compute_grad_slow,
assert H : (tgt ≠ (c, [])),
{
cases tgt with tgt_1 tgt_2,
dsimp at H_nin,
apply pair_neq_of_neq₁,
exact list.ne_of_not_mem_cons H_nin
},
simph,
dunfold list.sumr,
rw zero_add,
exact costs_helper cs tgt m (list.not_mem_of_not_mem_cons H_nin)
end

lemma compute_grad_slow_det_not_used_helper (costs : list ID) : Π (nodes : list node) (m : env) (tgt : reference),
is_not_used_downstream tgt nodes → tgt.1 ∉ costs →
compute_grad_slow costs nodes m tgt = 0
| [] m tgt H_not_used H_tgt_nin_costs :=
begin
apply costs_helper, all_goals { assumption }
end

| (⟨ref, parents, operator.det op⟩::nodes) m tgt H_not_used H_tgt_nin_costs :=
begin
dunfold compute_grad_slow,
dunfold is_not_used_downstream at H_not_used,
rw compute_grad_slow_det_not_used_helper nodes _ tgt H_not_used^.right H_tgt_nin_costs,
rw zero_add,
rw list.not_in_filter_of_match_riota,
reflexivity,
exact H_not_used^.left
end

| (⟨ref, parents, operator.rand op⟩::nodes) m tgt H_not_used H_tgt_nin_costs :=
begin
dunfold compute_grad_slow,
dunfold is_not_used_downstream at H_not_used,
rw compute_grad_slow_det_not_used_helper,
rw zero_add,
rw list.not_in_filter_of_match_riota,
reflexivity,
exact H_not_used^.left,
exact H_not_used^.right,
exact H_tgt_nin_costs
end

@[cgsimp] lemma compute_grad_slow_det_not_used (costs : list ID) (ref : reference) (parents : list reference) (op : det.op parents^.p2 ref^.2)
  : Π (nodes : list node) (m : env) (tgt : reference),
is_not_used_downstream tgt nodes → tgt.1 ∉ costs →
compute_grad_slow costs (⟨ref, parents, operator.det op⟩ :: nodes) m tgt
=
list.sumr (list.map (λ (idx : ℕ), op^.pb (env.get_ks parents m)
                                        (env.get ref m)
                                        (compute_grad_slow costs nodes m ref)
                                        idx
                                        tgt.2)
                    (list.filter (λ idx, tgt = list.dnth parents idx) (list.riota $ list.length parents))) :=
begin
intros nodes m tgt H_not_used H_tgt_nin_costs,
dunfold_occs compute_grad_slow [1],
rw [compute_grad_slow_det_not_used_helper _ _ _ _ H_not_used H_tgt_nin_costs, zero_add]
end

@[cgsimp] lemma compute_grad_slow_det_used (costs : list ID) (ref : reference) (parents : list reference) (op : det.op parents^.p2 ref^.2)
  : Π (nodes : list node) (m : env) (tgt : reference),
is_used_downstream tgt nodes ∨ tgt.1 ∈ costs →
compute_grad_slow costs (⟨ref, parents, operator.det op⟩ :: nodes) m tgt
=
compute_grad_slow costs nodes m tgt +
list.sumr (list.map (λ (idx : ℕ), op^.pb (env.get_ks parents m)
                                        (env.get ref m)
                                        (compute_grad_slow costs nodes m ref)
                                        idx
                                        tgt.2)
                    (list.filter (λ idx, tgt = list.dnth parents idx) (list.riota $ list.length parents))) :=
begin
intros nodes m tgt H_is_used_or_cost,
reflexivity
end

@[cgsimp] lemma compute_grad_slow_rand_not_used (costs : list ID) (ref : reference) (parents : list reference) (op : rand.op parents^.p2 ref^.2)
  : Π (nodes : list node) (m : env) (tgt : reference),
is_not_used_downstream tgt nodes → tgt.1 ∉ costs →
compute_grad_slow costs (⟨ref, parents, operator.rand op⟩ :: nodes) m tgt
=
list.sumr (list.map (λ (idx : ℕ), sum_downstream_costs nodes costs ref m ⬝ op^.glogpdf (env.get_ks parents m) (env.get ref m) idx tgt.2)
                   (list.filter (λ idx, tgt = list.dnth parents idx) (list.riota $ list.length parents))) :=
begin
intros nodes m tgt H_not_used H_tgt_nin_costs,
dunfold_occs compute_grad_slow [1],
rw [compute_grad_slow_det_not_used_helper _ _ _ _ H_not_used H_tgt_nin_costs, zero_add]
end

@[cgsimp] lemma compute_grad_slow_rand_used (costs : list ID) (ref : reference) (parents : list reference) (op : rand.op parents^.p2 ref^.2)
  : Π (nodes : list node) (m : env) (tgt : reference),
is_used_downstream tgt nodes ∨ tgt.1 ∈ costs →
compute_grad_slow costs (⟨ref, parents, operator.rand op⟩ :: nodes) m tgt
=
compute_grad_slow costs nodes m tgt +
list.sumr (list.map (λ (idx : ℕ), sum_downstream_costs nodes costs ref m ⬝ op^.glogpdf (env.get_ks parents m) (env.get ref m) idx tgt.2)
                   (list.filter (λ idx, tgt = list.dnth parents idx) (list.riota $ list.length parents))) :=
begin
intros nodes m tgt H_used_or_cost,
reflexivity
end

attribute [cgsimp] compute_grad_slow.equations._eqn_1

lemma grads_exist_at_simp_helper : Π (nodes : list node) (m : env) (tgt : reference),
  is_not_used_downstream tgt nodes → grads_exist_at nodes m tgt
| [] m tgt H_not_used := trivial

| (⟨ref, parents, operator.det op⟩::nodes) m tgt H_not_used :=
begin
dunfold grads_exist_at,
dunfold is_not_used_downstream at H_not_used,
dsimp,
split,
apply grads_exist_at_simp_helper nodes _ tgt H_not_used^.right,
intro H_in_parents,
exfalso,
exact H_not_used^.left H_in_parents
end

| (⟨ref, parents, operator.rand op⟩::nodes) m tgt H_not_used :=
begin
dunfold grads_exist_at,
dunfold is_not_used_downstream at H_not_used,
dsimp,
split,
intro H_in_parents,
exfalso,
exact H_not_used^.left H_in_parents,
intro y,
apply grads_exist_at_simp_helper nodes _ tgt H_not_used^.right
end

@[cgsimp] lemma grads_exist_at_det_not_used (ref : reference) (parents : list reference) (op : det.op parents^.p2 ref^.2)
  : Π (nodes : list node) (m : env) (tgt : reference),
is_not_used_downstream tgt nodes →
grads_exist_at (⟨ref, parents, operator.det op⟩ :: nodes) m tgt
=
let m' := env.insert ref (op^.f (env.get_ks parents m)) m in
(tgt ∈ parents → op^.pre (env.get_ks parents m) ∧ grads_exist_at nodes (env.insert ref (op^.f (env.get_ks parents m)) m) ref) :=
begin
intros nodes m tgt H_not_used,
dunfold grads_exist_at,
dsimp,
rw (pextt (grads_exist_at_simp_helper _ _ _ H_not_used)),
simp
end

@[cgsimp] lemma grads_exist_at_det_used (ref : reference) (parents : list reference) (op : det.op parents^.p2 ref^.2)
  : Π (nodes : list node) (m : env) (tgt : reference),
is_used_downstream tgt nodes →
grads_exist_at (⟨ref, parents, operator.det op⟩ :: nodes) m tgt
=
let m' := env.insert ref (op^.f (env.get_ks parents m)) m in
grads_exist_at nodes m' tgt ∧
(tgt ∈ parents → op^.pre (env.get_ks parents m) ∧ grads_exist_at nodes (env.insert ref (op^.f (env.get_ks parents m)) m) ref) :=
begin
intros nodes m tgt H, reflexivity
end

attribute [cgsimp] grads_exist_at.equations._eqn_1 grads_exist_at.equations._eqn_3

attribute [cgsimp] can_differentiate_under_integrals

attribute [cgsimp] T.smul_zero T.one_smul

attribute [cgsimp] if_pos if_neg if_true if_false

attribute [cgsimp] dif_pos dif_neg dif_ctx_simp_congr

attribute [cgsimp] mvn_iso_mvn_iso_empirical_kl_int mvn_iso_bernoulli_neglogpdf_int

attribute [cgsimp] force_ok

attribute [cgsimp] list.sumr list.map list.concat list.head list.tail list.riota list.filter list.length list.dnth
                   list.sublist.refl list.nil_subset list.sublist_cons list.cons_append list.append_nil list.nil_append
                   list.p1 list.p2

attribute [cgsimp] hash_map.find_insert_eq hash_map.find_insert_ne

attribute [cgsimp] zero_add add_zero

attribute [cgsimp] dvec.head dvec.head2 dvec.head3

attribute [cgsimp] integrate_kl integrate_mvn_iso_kl integrate_kl_pre integrate_mvn_iso_kl_pre reparameterize
attribute [cgsimp] reparam reparameterize reparameterize_pre

attribute [cgsimp] all_parents_in_env all_costs_scalars /- grads_exist_at -/ pdfs_exist_at uniq_ids
                   is_gintegrable is_nabla_gintegrable is_gdifferentiable /- can_differentiate_under_integrals -/

attribute [cgsimp] graph.to_dist operator.to_dist sum_costs /- compute_grad_slow -/

attribute [cgsimp] E.E_bind E.E_ret

attribute [cgsimp] ops.neg ops.exp ops.log ops.sqrt ops.add ops.sub ops.mul ops.div ops.sum
                   ops.gemm ops.sigmoid ops.softplus ops.scale ops.mul_add ops.mvn_iso_kl ops.bernoulli_neglogpdf

attribute [cgsimp] det.op.f ops.neg.f ops.exp.f ops.log.f ops.sqrt.f ops.add.f ops.sub.f ops.mul.f ops.div.f ops.sum.f
                   ops.gemm.f ops.sigmoid.f ops.softplus.f ops.scale.f ops.mul_add.f ops.mvn_iso_kl.f ops.bernoulli_neglogpdf.f

attribute [cgsimp] det.op.pre ops.neg.f_pre ops.exp.f_pre ops.log.f_pre ops.sqrt.f_pre ops.add.f_pre ops.sub.f_pre ops.mul.f_pre ops.div.f_pre ops.sum.f_pre
                   ops.gemm.f_pre ops.sigmoid.f_pre ops.softplus.f_pre ops.scale.f_pre ops.mul_add.f_pre ops.mvn_iso_kl.f_pre ops.bernoulli_neglogpdf.f_pre

attribute [cgsimp] det.op.pb ops.neg.f_pb ops.exp.f_pb ops.log.f_pb ops.sqrt.f_pb ops.add.f_pb ops.sub.f_pb ops.mul.f_pb ops.div.f_pb ops.sum.f_pb
                   ops.gemm.f_pb ops.sigmoid.f_pb ops.softplus.f_pb ops.scale.f_pb ops.mul_add.f_pb ops.mvn_iso_kl.f_pb ops.bernoulli_neglogpdf.f_pb

attribute [cgsimp] det.op.is_odiff det.op.pb_correct det.op.is_ocont

attribute [cgsimp] rand.op.pdf rand.pdf.mvn_iso rand.pdf.mvn_iso_std
                   rand.op.pre rand.op.mvn_iso rand.op.mvn_iso_std rand.pre.mvn_iso rand.pre.mvn_iso_std

attribute [cgsimp] env.get_ks env.insert_all env.get_insert_same env.get_insert_diff

attribute [cgsimp] list.insertion_sort list.ordered_insert

attribute [cgsimp] program_to_graph program.program_to_graph_core program.get_id
--                  program.unary_to_cwise1 program.binary_to_cwise2
                  program.process_term program.empty_state program.process_rterm
                  program_to_graph._match_1
                  program.program_to_graph_core._match_1
                  program.program_to_graph_core._match_2
                  program.process_rterm._match_1
                  program.process_term._match_6
                  program.process_term._match_10
                  program.process_term._match_13
--                  program.process_term._match_16
--                  program.process_term._match_17
                  program.exp program.log program.sqrt program.softplus program.sigmoid

@[cgsimp] lemma lift_t_label_to_term (x : label) : (lift_t x : program.term) = (program.term.id x) := rfl

namespace tactic
open tactic

meta def dcgsimp : tactic unit := do
  s ← join_user_simp_lemmas tt [`cgsimp],
  dsimp_core s

meta def gsimpt_core : Π (tac : tactic unit) (s : simp_lemmas) (e : expr), tactic (expr × expr) := λ tac s e,
do (a, new_tgt, pf) ← ext_simplify_core () {} s

(λ u, failed)
--pre
(λ a s r p e, failed)
--post
(λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core reducible s tac r e,
                 return ((), new_e, pr, tt))
`eq e,

  return (new_tgt, pf)

meta def gsimpt (tac : tactic unit) : tactic unit := do
  s ← join_user_simp_lemmas tt [`cgsimp],
  tgt ← target,
  (new_tgt, pf) ← gsimpt_core tac s tgt,
  replace_target new_tgt pf

meta def cgsimpt (tac : tactic unit) : tactic unit := do
  repeat $ first [gsimpt tac, prove_refs_neq, prove_ids_neq, triv]

meta def cgsimpn : ℕ → tactic unit
| 0 := cgsimpt skip
| (n+1) := cgsimpt (cgsimpn n)

meta def cgsimp : tactic unit := cgsimpn 100

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
     solve1 (cgsimp),
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
   -- TODO(dhs): async would be great but I run out of memory
   forall_idxs prove_model_base prove_model_step idx


end tactic
end certigrad
