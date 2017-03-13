/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Proof that Certigrad is correct on a specific autoencoding variational Bayes (AEVB) graph.

Warning: this file is very slow to compile.
-/
import system.io .tensor .compute_grad .graph .tvec .optim .run_utils .expected_value .reparam .kl .tfacts .backprop_correct .env .aevb_tactics .program

-- set_option class.instance_max_depth 5000

namespace certigrad
namespace aevb

open list

structure aevb_arch : Type := (bs n_x n_in nz ne nd : ℕ)

structure weights (arch : aevb_arch) : Type :=
  (bstart : ℝ)
  (he : T [arch^.ne, arch^.n_in])
  (he_μ : T [arch^.nz, arch^.ne])
  (he_logσ₂ : T [arch^.nz, arch^.ne])
  (hd : T [arch^.nd, arch^.nz])
  (hd_γ : T [arch^.n_in, arch^.nd])

--@[gsimp] def mk_input_dict : Π {arch : aevb_arch} (ws : weights arch) (g : graph), env
--| arch ws g := env.insert_all g^.inputs ⟦ws^.bstart, ws^.he, ws^.he_μ, ws^.he_logσ₂, ws^.hd, ws^.hd_γ⟧

section program
open certigrad.program certigrad.program.statement certigrad.program.term certigrad.program.rterm list label

@[gsimp] def prog_naive : Π (arch : aevb_arch) (x_data : T [arch^.n_in, arch^.n_x]), program | arch x_data :=

[
input batch_start     [],
param W_encode        [arch^.ne, arch^.n_in],
param W_encode_μ      [arch^.nz, arch^.ne],
param W_encode_log_σ₂ [arch^.nz, arch^.ne],
param W_decode        [arch^.nd, arch^.nz],
param W_decode_p      [arch^.n_in, arch^.nd],

assign x             $ get_col_range (const x_data) batch_start arch^.bs,
assign h_encode      $ softplus (gemm W_encode x),
assign μ             $ gemm W_encode_μ h_encode,
assign σ             $ sqrt (exp (gemm W_encode_log_σ₂ h_encode)),
sample z             $ mvn_iso μ σ,
assign encoding_loss $ mvn_iso_empirical_kl μ σ z,
assign p             $ sigmoid (gemm  W_decode_p (softplus (gemm W_decode z))),
assign decoding_loss $ bernoulli_neglogpdf p x,

cost encoding_loss,
cost decoding_loss
]

@[gsimp] def build_graph : Π (arch : aevb_arch) (x_data : T [arch^.n_in, arch^.n_x]), graph
| arch x_data := program_to_graph (prog_naive arch x_data)

open certigrad.det
open certigrad.det.cwise1
open certigrad.det.cwise2
open certigrad.det.special
open rand.op
open tactic

lemma build_graph.unfold (arch : aevb_arch) (x_data : T [arch^.n_in, arch^.n_x]) :
build_graph arch x_data =
graph.mk [⟨(0, [arch^.n_in, arch^.n_x]), [], operator.det $ op.const x_data⟩,
          ⟨(x, [arch^.n_in, arch^.bs]), [(0, [arch^.n_in, arch^.n_x]), (batch_start, [])], operator.det $ op.special $ get_col_range _ _ _⟩,
          ⟨(2, [arch^.ne, arch^.bs]), [(W_encode, [arch^.ne, arch^.n_in]), (x, [arch^.n_in, arch^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(h_encode, [arch^.ne, arch^.bs]), [(2, [arch^.ne, arch^.bs])], operator.det $ op.unary $ softplus⟩,
          ⟨(μ, [arch^.nz, arch^.bs]), [(W_encode_μ, [arch^.nz, arch^.ne]), (h_encode, [arch^.ne, arch^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(5, [arch^.nz, arch^.bs]), [(W_encode_log_σ₂, [arch^.nz, arch^.ne]), (h_encode, [arch^.ne, arch^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(6, [arch^.nz, arch^.bs]), [(5, [arch^.nz, arch^.bs])], operator.det $ op.unary exp⟩,
          ⟨(σ, [arch^.nz, arch^.bs]), [(6, [arch^.nz, arch^.bs])], operator.det $ op.unary sqrt⟩,
          ⟨(z, [arch^.nz, arch^.bs]), [(μ, [arch^.nz, arch^.bs]), (σ, [arch^.nz, arch^.bs])], operator.rand $ mvn_iso _⟩,
          ⟨(encoding_loss, []), [(μ, [arch^.nz, arch^.bs]), (σ, [arch^.nz, arch^.bs]), (z, [arch^.nz, arch^.bs])], operator.det $ op.mvn_iso_empirical_kl _⟩,
          ⟨(10, [arch^.nd, arch^.bs]), [(W_decode, [arch^.nd, arch^.nz]), (z, [arch^.nz, arch^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(11, [arch^.nd, arch^.bs]), [(10, [arch^.nd, arch^.bs])], operator.det $ op.unary $ softplus⟩,
          ⟨(12, [arch^.n_in, arch^.bs]), [(W_decode_p, [arch^.n_in, arch^.nd]), (11, [arch^.nd, arch^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(p, [arch^.n_in, arch^.bs]), [(12, [arch^.n_in, arch^.bs])], operator.det $ op.unary $ sigmoid⟩,
          ⟨(decoding_loss, []), [(p, [arch^.n_in, arch^.bs]), (x, [arch^.n_in, arch^.bs])], operator.det $ op.special $ bernoulli_neglogpdf _⟩]
         [encoding_loss, decoding_loss]
         [(W_encode, [arch.ne, arch.n_in]), (W_encode_μ, [arch.nz, arch.ne]), (W_encode_log_σ₂, [arch.nz, arch.ne]),
          (W_decode, [arch.nd, arch.nz]), (W_decode_p, [arch.n_in, arch.nd])]
         [(batch_start, []), (W_encode, [arch.ne, arch.n_in]), (W_encode_μ, [arch.nz, arch.ne]),
          (W_encode_log_σ₂, [arch.nz, arch.ne]), (W_decode, [arch.nd, arch.nz]), (W_decode_p, [arch.n_in, arch.nd])] :=
begin
tactic.dhsimp,
dsimp,
reflexivity
end

end program

#exit
--by gsimp ; dsimp

section ex
open tactic
example (arch : aevb_arch) (x_data : T [arch^.n_in, arch^.n_x]) :
  build_graph arch x_data = sorry :=
begin
tactic.gsimp,
dsimp with gsimp,
end
end ex
#exit

namespace theorems
open certigrad.tactic tactic graph list

parameters (arch : aevb_arch) (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x])
def g : graph := build_graph arch x_data
def fdict : env := mk_input_dict g

lemma g_integrate_mvn_pre : integrate_kl_pre g := sorry

lemma g_nodups : nodup (env.keys fdict ++ map node.ref g^.nodes) := sorry --by dec_triv

lemma g_ps_in_env : all_parents_in_env fdict g^.nodes := sorry -- by gsimp

--sorry  --by prove_all_ps_in_env

lemma g_pdfs_exist : pdfs_exist_at g^.nodes fdict := sorry --by gsimp

lemma g_gint : is_gintegrable (λ m, ⟦sum_costs m g^.costs⟧) fdict g^.nodes dvec.head := sorry --by gsimp

lemma g_kl_gint : is_gintegrable (λ m, ⟦sum_costs m (integrate_kl g)^.costs⟧) fdict (integrate_kl g)^.nodes dvec.head := sorry -- by gsimp

lemma integrate_kl_sound :
E (graph.to_dist (λ m, ⟦sum_costs m (integrate_kl g)^.costs⟧) fdict (integrate_kl g)^.nodes) dvec.head
=
E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) fdict g^.nodes dvec.head :=
integrate_mvn_iso_kl_correct "el" ["dl"] g^.nodes _ dec_trivial
                             g_integrate_mvn_pre g_nodups g_ps_in_env
                             g_pdfs_exist g_kl_gint g_gint

#exit

lemma g_kl_reparameterize_pre {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  reparameterize_pre [arch^.nz, arch^.bs] (g_kl p x_data)^.nodes (mk_input_dict ws) := sorry -- by gsimp

lemma g_kl_nodups {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  nodup (env.keys (mk_input_dict ws) ++ map node.ref (g_kl p x_data)^.nodes) := sorry -- by dec_triv

lemma g_kl_ps_in_env {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  all_parents_in_env (mk_input_dict ws) (g_kl p x_data)^.nodes := sorry -- by gsimp

lemma g_kl_ε_fresh {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  (ID.str "ε", [arch^.nz, arch^.bs]) ∉ env.keys (mk_input_dict ws) ++ map node.ref (g_kl p x_data)^.nodes := sorry -- by dec_triv

lemma reparameterize_sound {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
E (graph.to_dist (λ m, ⟦sum_costs m (g_final p x_data)^.costs⟧) (mk_input_dict ws) (g_final p x_data)^.nodes) dvec.head
=
E (graph.to_dist (λ m, ⟦sum_costs m (g_kl p x_data)^.costs⟧) (mk_input_dict ws) (g_kl p x_data)^.nodes) dvec.head :=
reparameterize_correct (ID.str "ε", [arch^.nz, arch^.bs]) (g_kl_reparameterize_pre ws x_data) (g_kl_nodups ws x_data)
                       (g_kl_ps_in_env ws x_data) (g_kl_ε_fresh ws x_data) dec_trivial

lemma aevb_correct {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
E (graph.to_dist (λ m, ⟦sum_costs m (g_final p x_data)^.costs⟧) (mk_input_dict ws) (g_final p x_data)^.nodes) dvec.head
=
E (graph.to_dist (λ m, ⟦sum_costs m (g p x_data)^.costs⟧) (mk_input_dict ws) (g p x_data)^.nodes) dvec.head :=
by rw [reparameterize_sound, integrate_kl_sound]

lemma g_final_nodups {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) : nodup (env.keys (mk_input_dict ws) ++ map node.ref (g_final p x_data)^.nodes) := sorry --by dec_triv

lemma g_final_ps_in_env {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) : all_parents_in_env (mk_input_dict ws) (g_final p x_data)^.nodes := sorry -- by gsimp

lemma g_final_pdfs_exist_at {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) : pdfs_exist_at (g_final p x_data)^.nodes (mk_input_dict ws) := sorry -- by gsimp


lemma g_final_costs_scalars {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) : all_costs_scalars (g_final p x_data)^.costs (g_final p x_data)^.nodes :=
begin
gsimp,
exact dec_trivial
end

example : [(ID.str "he", @nil ℕ)] ⊆ [(ID.str "he", @nil ℕ), (ID.str "hg", ([5] : S))] :=
begin
dunfold has_subset.subset list.subset,
exact dec_trivial
end

instance {xs ys : list reference} : decidable (xs ⊆ ys) :=
begin
dunfold has_subset.subset list.subset,
apply_instance
end

lemma g_final_tgts_in_inputs {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) : (g_final p x_data)^.targets ⊆ env.keys (mk_input_dict ws) :=
begin
dsimp with gsimp,
dsimp [env.keys, env.insert, dmap.insert, pdmap.insert, env.mk, dmap.mk, dmap.keys, pdmap.keys, pdmap.mk, insertion_sort],


--exact dec_trivial

end

/-
have H_keys : env.keys (mk_input_dict ws) =
[(ID.str "hels2", [arch^.nz, arch^.ne]), (ID.str "hd", [arch^.nd, arch^.nz]), (ID.str "he", [arch^.ne, arch^.n_in]),
 (ID.str "hg", [arch^.n_in, arch^.nd]), (ID.str "hem", [arch^.nz, arch^.ne]), (ID.str "bstart", [])], by reflexivity,
begin rw H_keys, dsimp, prove_sublist end
-/

-- env_has_key
lemma g_final_env_has_key_he {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  env.has_key ("he", [arch^.ne, arch^.n_in]) (mk_input_dict ws) := sorry -- by prove_contains

lemma g_final_env_has_key_hem {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  env.has_key ("hem", [arch^.nz, arch^.ne]) (mk_input_dict ws) := sorry -- by prove_contains

lemma g_final_env_has_key_hels2 {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  env.has_key ("hels2", [arch^.nz, arch^.ne]) (mk_input_dict ws) := sorry -- by prove_contains

lemma g_final_env_has_key_hd {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  env.has_key ("hd", [arch^.nd, arch^.nz]) (mk_input_dict ws) := sorry -- by prove_contains

lemma g_final_env_has_key_hg {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  env.has_key ("hg", [arch^.n_in, arch^.nd]) (mk_input_dict ws) := sorry -- by prove_contains

-- tgt_cost_scalar
lemma g_final_tgt_cost_scalar_he {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  ID.str "he" ∈ (g_final p x_data)^.costs → [arch^.ne, arch^.n_in] = [] := sorry -- by dec_triv

lemma g_final_tgt_cost_scalar_hem {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  ID.str "hem" ∈ (g_final p x_data)^.costs → [arch^.nz, arch^.ne] = [] := sorry -- by dec_triv

lemma g_final_tgt_cost_scalar_hels2 {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  ID.str "hels2" ∈ (g_final p x_data)^.costs → [arch^.nz, arch^.ne] = [] := sorry -- by dec_triv

lemma g_final_tgt_cost_scalar_hd {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  ID.str "hd" ∈ (g_final p x_data)^.costs → [arch^.nd, arch^.nz] = [] := sorry -- by dec_triv

lemma g_final_tgt_cost_scalar_hg {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  ID.str "hg" ∈ (g_final p x_data)^.costs → [arch^.n_in, arch^.nd] = [] := sorry -- by dec_triv

-- well_formed_at
/-

("hem", [arch^.nz, arch^.ne])
("hels2", [arch^.nz, arch^.ne])
("hd", [arch^.nd, arch^.nz])
("hg", [arch^.n_in, arch^.nd])
-/

lemma g_final_tgt_wf_at_he {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  well_formed_at (g_final p x_data)^.costs (g_final p x_data)^.nodes (mk_input_dict ws) ("he", [arch^.ne, arch^.n_in]) := sorry -- already proved components

lemma g_final_tgt_wf_at_hem {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  well_formed_at (g_final p x_data)^.costs (g_final p x_data)^.nodes (mk_input_dict ws) ("hem", [arch^.nz, arch^.ne]) := sorry -- already proved components

lemma g_final_tgt_wf_at_hels2 {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  well_formed_at (g_final p x_data)^.costs (g_final p x_data)^.nodes (mk_input_dict ws) ("hels2", [arch^.nz, arch^.ne]) := sorry -- already proved components

lemma g_final_tgt_wf_at_hd {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  well_formed_at (g_final p x_data)^.costs (g_final p x_data)^.nodes (mk_input_dict ws) ("hd", [arch^.nd, arch^.nz]) := sorry -- already proved components

lemma g_final_tgt_wf_at_hg {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  well_formed_at (g_final p x_data)^.costs (g_final p x_data)^.nodes (mk_input_dict ws) ("hg", [arch^.n_in, arch^.nd]) := sorry -- already proved components

-- grads_exist_at
lemma g_final_grads_exist_at_he {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  grads_exist_at (g_final p x_data)^.nodes (mk_input_dict ws) ("he", [arch^.ne, arch^.n_in]) := sorry

lemma g_final_grads_exist_at_hem {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  grads_exist_at (g_final p x_data)^.nodes (mk_input_dict ws) ("hem", [arch^.nz, arch^.ne]) := sorry

lemma g_final_grads_exist_at_hels2 {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  grads_exist_at (g_final p x_data)^.nodes (mk_input_dict ws) ("hels2", [arch^.nz, arch^.ne]) := sorry

lemma g_final_grads_exist_at_hd {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  grads_exist_at (g_final p x_data)^.nodes (mk_input_dict ws) ("hd", [arch^.nd, arch^.nz]) := sorry

lemma g_final_grads_exist_at_hg {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  grads_exist_at (g_final p x_data)^.nodes (mk_input_dict ws) ("hg", [arch^.n_in, arch^.nd]) := sorry

-- is_gintegrable
lemma g_final_is_gintegrable_he {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  is_gintegrable (λ m, ⟦compute_grad_slow (g_final p x_data)^.costs (g_final p x_data)^.nodes m ("he", [arch^.ne, arch^.n_in])⟧)
                 (mk_input_dict ws) (g_final p x_data)^.nodes dvec.head := sorry

/-
begin
--dunfold is_nabla_gintegrable is_gintegrable graph.to_dist operator.to_dist sum_costs compute_grad_slow sumr map ,
--dget_dinsert_concrete,

/-simp [env.get_ks, rand.op.pdf, det.op.f, det.special.f, det.function.gemm,
      dvec.head, dvec.head2, dvec.head3, E.E_bind, E.E_ret,
      det.function.bernoulli_neglogpdf, det.function.get_col_range,
      det.function.mvn_iso_empirical_kl, det.op.f.equations._eqn_2
 ],
-/
/-

dsimp [dvec.head, dvec.head2, dvec.head3],
dget_dinsert,
simp only [det.op.f, det.cwise1.f, rand.op.pdf, rand.pdf.mvn_iso, det.function.sqrt, det.function.exp, det.function.sigmoid, det.function.softplus, rand.pdf.mvn_iso_std,
       det.function.mul_add, det.function.mvn_iso_kl],
dsimp [dvec.head, dvec.head2, dvec.head3],
-/

end
-/

lemma g_final_is_gintegrable_hem {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  is_gintegrable (λ m, ⟦compute_grad_slow (g_final p x_data)^.costs (g_final p x_data)^.nodes m ("hem", [arch^.nz, arch^.ne])⟧)
                 (mk_input_dict ws) (g_final p x_data)^.nodes dvec.head := sorry

lemma g_final_is_gintegrable_hels2 {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  is_gintegrable (λ m, ⟦compute_grad_slow (g_final p x_data)^.costs (g_final p x_data)^.nodes m ("hels2", [arch^.nz, arch^.ne])⟧)
                 (mk_input_dict ws) (g_final p x_data)^.nodes dvec.head := sorry

lemma g_final_is_gintegrable_hd {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  is_gintegrable (λ m, ⟦compute_grad_slow (g_final p x_data)^.costs (g_final p x_data)^.nodes m ("hd", [arch^.nd, arch^.nz])⟧)
                 (mk_input_dict ws) (g_final p x_data)^.nodes dvec.head := sorry

lemma g_final_is_gintegrable_hg {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  is_gintegrable (λ m, ⟦compute_grad_slow (g_final p x_data)^.costs (g_final p x_data)^.nodes m ("hg", [arch^.n_in, arch^.nd])⟧)
                 (mk_input_dict ws) (g_final p x_data)^.nodes dvec.head := sorry
-- diff_under_int
lemma g_final_diff_under_int_hem {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  can_differentiate_under_integrals (g_final p x_data)^.costs (g_final p x_data)^.nodes (mk_input_dict ws) ("hem", [arch^.nz, arch^.ne]) := sorry
/-
begin
dsimp [can_differentiate_under_integrals, is_nabla_gintegrable, is_gintegrable, graph.to_dist, operator.to_dist, sum_costs, compute_grad_slow, sumr, map],
dget_dinsert_cheat,
simp only [env.get_ks, rand.op.pdf, det.op.f, det.special.f, det.function.gemm,
      dvec.head, dvec.head2, dvec.head3, E.E_bind, E.E_ret,
      det.function.bernoulli_neglogpdf, det.function.get_col_range,
      det.function.mvn_iso_empirical_kl, det.op.f.equations._eqn_2, det.function.mvn_iso_kl, det.function.mul_add,
      det.cwise1.f, det.function.sigmoid, det.function.softplus, det.function.sqrt, det.function.exp
],
-- all obligations will be trivial!
cheat_pis
all_goals { exact sorry }
end
-/
lemma g_final_diff_under_int_hels2 {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  can_differentiate_under_integrals (g_final p x_data)^.costs (g_final p x_data)^.nodes (mk_input_dict ws) ("hels2", [arch^.nz, arch^.ne]) := sorry

lemma g_final_diff_under_int_hd {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  can_differentiate_under_integrals (g_final p x_data)^.costs (g_final p x_data)^.nodes (mk_input_dict ws) ("hd", [arch^.nd, arch^.nz]) := sorry

lemma g_final_diff_under_int_hg {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  can_differentiate_under_integrals (g_final p x_data)^.costs (g_final p x_data)^.nodes (mk_input_dict ws) ("hg", [arch^.n_in, arch^.nd]) := sorry

lemma g_final_diff_under_int_he {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
  can_differentiate_under_integrals (g_final p x_data)^.costs (g_final p x_data)^.nodes (mk_input_dict ws) ("he", [arch^.ne, arch^.n_in]) := sorry

-- total, by tgt
lemma g_final_backprop_correct_he {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
let g : graph := g_final p x_data,
    init_dict : env := compute_init_dict g^.costs g^.nodes g^.targets,
    inputs : env := mk_input_dict ws,
    tgt : reference := ("he", [arch^.ne, arch^.n_in]),
    idx := 0 in
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ inputs) g^.nodes) dvec.head) (env.get tgt inputs)
=
E (graph.to_dist (λ m, backprop g^.costs init_dict g^.nodes m g^.targets) inputs g^.nodes) (λ dict, dvec.get tgt.2 dict idx) := sorry

lemma g_final_backprop_correct_hem {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
let g : graph := g_final p x_data,
    init_dict : env := compute_init_dict g^.costs g^.nodes g^.targets,
    inputs : env := mk_input_dict ws,
    tgt : reference := ("hem", [arch^.nz, arch^.ne]),
    idx := 1 in
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ inputs) g^.nodes) dvec.head) (env.get tgt inputs)
=
E (graph.to_dist (λ m, backprop g^.costs init_dict g^.nodes m g^.targets) inputs g^.nodes) (λ dict, dvec.get tgt.2 dict idx) := sorry

lemma g_final_backprop_correct_hels2 {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
let g : graph := g_final p x_data,
    init_dict : env := compute_init_dict g^.costs g^.nodes g^.targets,
    inputs : env := mk_input_dict ws,
    tgt : reference := ("hels2", [arch^.nz, arch^.ne]),
    idx := 2 in
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ inputs) g^.nodes) dvec.head) (env.get tgt inputs)
=
E (graph.to_dist (λ m, backprop g^.costs init_dict g^.nodes m g^.targets) inputs g^.nodes) (λ dict, dvec.get tgt.2 dict idx) := sorry

lemma g_final_backprop_correct_hd {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
let g : graph := g_final p x_data,
    init_dict : env := compute_init_dict g^.costs g^.nodes g^.targets,
    inputs : env := mk_input_dict ws,
    tgt : reference := ("hd", [arch^.nd, arch^.nz]),
    idx := 3 in
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ inputs) g^.nodes) dvec.head) (env.get tgt inputs)
=
E (graph.to_dist (λ m, backprop g^.costs init_dict g^.nodes m g^.targets) inputs g^.nodes) (λ dict, dvec.get tgt.2 dict idx) := sorry

lemma g_final_backprop_correct_hg {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
let g : graph := g_final p x_data,
    init_dict : env := compute_init_dict g^.costs g^.nodes g^.targets,
    inputs : env := mk_input_dict ws,
    tgt : reference := ("hg", [arch^.n_in, arch^.nd]),
    idx := 4 in
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ inputs) g^.nodes) dvec.head) (env.get tgt inputs)
=
E (graph.to_dist (λ m, backprop g^.costs init_dict g^.nodes m g^.targets) inputs g^.nodes) (λ dict, dvec.get tgt.2 dict idx) := sorry

theorem aevb_gradients_correct_full {arch : aevb_arch} (ws : weights p) (x_data : T [arch^.n_in, arch^.n_x]) :
∀ (tgt : reference) (idx : ℕ), at_idx (g_final p x_data)^.targets idx tgt →
let g : graph := g_final p x_data in
let init_dict : env := compute_init_dict g^.costs g^.nodes g^.targets in
let inputs : env := mk_input_dict ws in
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ inputs) g^.nodes) dvec.head) (env.get tgt inputs)
=
E (graph.to_dist (λ m, backprop g^.costs init_dict g^.nodes m g^.targets) inputs g^.nodes) (λ dict, dvec.get tgt.2 dict idx)
| tgt 0     H_at_idx := begin intros g init_dict inputs, rw (and.right H_at_idx), exact g_final_backprop_correct_he ws x_data end
| tgt 1     H_at_idx := begin intros g init_dict inputs, rw (and.right H_at_idx), exact g_final_backprop_correct_hem ws x_data end
| tgt 2     H_at_idx := begin intros g init_dict inputs, rw (and.right H_at_idx), exact g_final_backprop_correct_hels2 ws x_data end
| tgt 3     H_at_idx := begin intros g init_dict inputs, rw (and.right H_at_idx), exact g_final_backprop_correct_hd ws x_data end
| tgt 4     H_at_idx := begin intros g init_dict inputs, rw (and.right H_at_idx), exact g_final_backprop_correct_hg ws x_data end
| tgt (n+5) H_at_idx := false.rec _ (at_idx_over H_at_idx (by dec_triv))

end theorems
end aevb
end certigrad
