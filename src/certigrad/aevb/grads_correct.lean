/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Proofs that integrating out the KL and reparametizing are sound when
applied to the naive variational encoder.
-/
import .util .naive ..prove_model_ok ..pre ..backprop_correct

set_option max_memory 4096
--set_option pp.max_depth 100000
--set_option pp.max_steps 10000000

namespace certigrad
namespace aevb

section proofs
open graph list tactic certigrad.tactic

parameters (a : arch) (ws : weights a) (x_data : T [a^.n_in, a^.n_x])
def g : graph := reparam (integrate_kl $ graph_naive a x_data)
def fdict : env := mk_input_dict ws g

attribute [cgsimp] g fdict
/-
#print "wf..."
lemma g_final_tgt_wf_at_he : well_formed_at g^.costs g^.nodes fdict (ID.str label.W_encode, [a^.ne, a^.n_in]) := begin constructor, all_goals { cgsimp } end

#print "tgts_in_inputs..."
lemma g_final_tgts_in_inputs : g^.targets ⊆ env.keys fdict := by cgsimp

#print "pdfs_exist_at..."
lemma g_final_pdfs_exist_at : pdfs_exist_at g^.nodes fdict := by cgsimp

#print "grads_exist_at_he..."
lemma g_final_grads_exist_at_he : grads_exist_at g^.nodes fdict (ID.str label.W_encode, [a^.ne, a^.n_in]) := by cgsimp

#print "grads_exist_at_hem..."
lemma g_final_grads_exist_at_hem : grads_exist_at g^.nodes fdict (ID.str label.W_encode_μ, [a^.nz, a^.ne]) := by cgsimp

#print "grads_exist_at_hels₂..."
lemma g_final_grads_exist_at_hels₂ : grads_exist_at g^.nodes fdict (ID.str label.W_encode_logσ₂, [a^.nz, a^.ne]) := by cgsimp
-/

#print "grads_exist_at_hd..."
lemma g_final_grads_exist_at_hd : grads_exist_at g^.nodes fdict (ID.str label.W_decode, [a^.nd, a^.nz]) := by cgsimp
/-
#print "grads_exist_at_hdp..."
lemma g_final_grads_exist_at_hdp : grads_exist_at g^.nodes fdict (ID.str label.W_decode_p, [a^.n_in, a^.nd]) := by cgsimp

#print "gintegrable_he..."
lemma g_final_is_gintegrable_he :
  is_gintegrable (λ m, ⟦compute_grad_slow g^.costs g^.nodes m (ID.str label.W_encode, [a^.ne, a^.n_in])⟧)
                 fdict g^.nodes dvec.head := by cgsimp >> prove_is_mvn_integrable

#print "gintegrable_hem..."
lemma g_final_is_gintegrable_hem :
  is_gintegrable (λ m, ⟦compute_grad_slow g^.costs g^.nodes m (ID.str label.W_encode_μ, [a^.nz, a^.ne])⟧)
                 fdict g^.nodes dvec.head := by cgsimp >> prove_is_mvn_integrable

#print "gintegrable_hels₂..."
lemma g_final_is_gintegrable_hels₂ :
  is_gintegrable (λ m, ⟦compute_grad_slow g^.costs g^.nodes m (ID.str label.W_encode_logσ₂, [a^.nz, a^.ne])⟧)
                 fdict g^.nodes dvec.head := by cgsimp >> prove_is_mvn_integrable
-/
#print "gintegrable_hd..."
lemma g_final_is_gintegrable_hd :
  is_gintegrable (λ m, ⟦compute_grad_slow g^.costs g^.nodes m (ID.str label.W_decode, [a^.nd, a^.nz])⟧)
                 fdict g^.nodes dvec.head := by cgsimp >> prove_is_mvn_integrable
/-
#print "gintegrable_hdp..."
lemma g_final_is_gintegrable_hdp :
  is_gintegrable (λ m, ⟦compute_grad_slow g^.costs g^.nodes m (ID.str label.W_decode_p, [a^.n_in, a^.nd])⟧)
                 fdict g^.nodes dvec.head := by cgsimp >> prove_is_mvn_integrable

#print "can_diff_he..."
lemma g_final_diff_under_int_he :
  can_differentiate_under_integrals g^.costs g^.nodes fdict (ID.str label.W_encode, [a^.ne, a^.n_in]) :=
by cgsimp >> prove_is_mvn_uintegrable

#print "can_diff_hem..."
lemma g_final_diff_under_int_hem :
  can_differentiate_under_integrals g^.costs g^.nodes fdict (ID.str label.W_encode_μ, [a^.nz, a^.ne]) :=
by cgsimp >> prove_is_mvn_uintegrable

#print "can_diff_hels₂..."
lemma g_final_diff_under_int_hels₂ :
  can_differentiate_under_integrals g^.costs g^.nodes fdict (ID.str label.W_encode_logσ₂, [a^.nz, a^.ne]) :=
by cgsimp >> prove_is_mvn_uintegrable
-/
#print "can_diff_hd..."
lemma g_final_diff_under_int_hd :
  can_differentiate_under_integrals g^.costs g^.nodes fdict (ID.str label.W_decode, [a^.nd, a^.nz]) :=
by cgsimp >> prove_is_mvn_uintegrable
/-
#print "can_diff_hdp..."
lemma g_final_diff_under_int_hdp :
  can_differentiate_under_integrals g^.costs g^.nodes fdict (ID.str label.W_decode_p, [a^.n_in, a^.nd]) :=
by cgsimp >> prove_is_mvn_uintegrable

lemma aevb_backprop_correct :
∀ (tgt : reference) (idx : ℕ), at_idx g^.targets idx tgt →
let init_dict : env := compute_init_dict g^.costs g^.nodes g^.targets in
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ fdict) g^.nodes) dvec.head) (env.get tgt fdict)
=
E (graph.to_dist (λ m, backprop g^.costs init_dict g^.nodes m g^.targets) fdict g^.nodes) (λ dict, dvec.get tgt.2 dict idx)
| tgt 0     H_at_idx :=
begin
intros init_dict, rw (and.right H_at_idx),
apply backprop_correct,
-- TODO(dhs): make this one tactic
end

| tgt 1     H_at_idx := sorry
| tgt 2     H_at_idx := sorry
| tgt 3     H_at_idx := sorry
| tgt 4     H_at_idx := sorry
| tgt (n+5) H_at_idx := false.rec _ (at_idx_over H_at_idx (by dec_triv))


end proofs

-/
end aevb
end certigrad
