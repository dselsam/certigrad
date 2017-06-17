/-
1;4205;0cCopyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Proofs that integrating out the KL and reparametizing are sound when
applied to the naive variational encoder.
-/
import .util .naive ..prove_model_ok ..pre

set_option max_memory 4096
set_option pp.max_depth 100000
set_option pp.max_steps 10000000

namespace certigrad
namespace aevb

section proofs
open graph list tactic certigrad.tactic

parameters (a : arch) (ws : weights a) (x_data : T [a^.n_in, a^.n_x])
def g : graph := reparam (integrate_kl $ graph_naive a x_data)
def fdict : env := mk_input_dict ws g

attribute [cgsimp] g fdict

lemma g_final_nodups : nodup (env.keys fdict ++ map node.ref g^.nodes) := sorry -- by cgsimp

lemma g_final_ps_in_env : all_parents_in_env fdict g^.nodes := sorry --by cgsimp

lemma g_final_costs_scalars : all_costs_scalars g^.costs g^.nodes := sorry --by cgsimp

lemma g_final_env_has_key_he : env.has_key (ID.str label.W_encode, [a^.ne, a^.n_in]) fdict := sorry --by cgsimp

lemma g_final_tgt_cost_scalar_he : (ID.str label.W_encode ∈ g^.costs) → [a^.ne, a^.n_in] = [] := sorry --by cgsimp

lemma g_final_tgt_wf_at_he : well_formed_at g^.costs g^.nodes fdict (ID.str label.W_encode, [a^.ne, a^.n_in]) := sorry -- by constructor >> all_goals cgsimp

lemma g_final_tgts_in_inputs : g^.targets ⊆ env.keys fdict := sorry --by cgsimp

lemma g_final_pdfs_exist_at : pdfs_exist_at g^.nodes fdict := sorry --by cgsimp

-- TODO(dhs): The tactic is fast, but have yet to finish type-checking the proof
lemma g_final_grads_exist_at_he : grads_exist_at g^.nodes fdict (ID.str label.W_encode, [a^.ne, a^.n_in]) := sorry -- by cgsimp

lemma g_final_grads_exist_at_hem : grads_exist_at g^.nodes fdict (ID.str label.W_encode_μ, [a^.nz, a^.ne]) := sorry -- by cgsimp

lemma g_final_grads_exist_at_hels₂ : grads_exist_at g^.nodes fdict (ID.str label.W_encode_logσ₂, [a^.nz, a^.ne]) := sorry -- by cgsimp

lemma g_final_grads_exist_at_hd : grads_exist_at g^.nodes fdict (ID.str label.W_decode, [a^.nd, a^.nz]) := sorry -- by cgsimp

lemma g_final_grads_exist_at_hdp : grads_exist_at g^.nodes fdict (ID.str label.W_decode_p, [a^.n_in, a^.nd]) := sorry -- by cgsimp

-- TODO(dhs): this one works now but is slow
lemma g_final_is_gintegrable_he :
  is_gintegrable (λ m, ⟦compute_grad_slow g^.costs g^.nodes m (ID.str label.W_encode, [a^.ne, a^.n_in])⟧)
                 fdict g^.nodes dvec.head := sorry -- by cgsimp >> prove_is_mvn_integrable

lemma g_final_is_gintegrable_hem :
  is_gintegrable (λ m, ⟦compute_grad_slow g^.costs g^.nodes m (ID.str label.W_encode_μ, [a^.nz, a^.ne])⟧)
                 fdict g^.nodes dvec.head := sorry -- by cgsimp >> prove_is_mvn_integrable

lemma g_final_is_gintegrable_hels₂ :
  is_gintegrable (λ m, ⟦compute_grad_slow g^.costs g^.nodes m (ID.str label.W_encode_logσ₂, [a^.nz, a^.ne])⟧)
                 fdict g^.nodes dvec.head := sorry -- by cgsimp >> prove_is_mvn_integrable

lemma g_final_is_gintegrable_hd :
  is_gintegrable (λ m, ⟦compute_grad_slow g^.costs g^.nodes m (ID.str label.W_decode, [a^.nd, a^.nz])⟧)
                 fdict g^.nodes dvec.head := sorry -- by cgsimp >> prove_is_mvn_integrable

lemma g_final_is_gintegrable_hdp :
  is_gintegrable (λ m, ⟦compute_grad_slow g^.costs g^.nodes m (ID.str label.W_decode_p, [a^.n_in, a^.nd])⟧)
                 fdict g^.nodes dvec.head := sorry -- by cgsimp >> prove_is_mvn_integrable

lemma g_final_diff_under_int_he :
  can_differentiate_under_integrals g^.costs g^.nodes fdict (ID.str label.W_encode, [a^.ne, a^.n_in]) :=
by cgsimp >> prove_is_mvn_uintegrable >> trace "DONE" >> tactic.failed

lemma g_final_diff_under_int_hem :
  can_differentiate_under_integrals g^.costs g^.nodes fdict (ID.str label.W_encode_μ, [a^.nz, a^.ne]) :=
by cgsimp >> prove_is_mvn_uintegrable >> trace "DONE" >> tactic.failed

lemma g_final_diff_under_int_hels₂ :
  can_differentiate_under_integrals g^.costs g^.nodes fdict (ID.str label.W_encode_logσ₂, [a^.nz, a^.ne]) :=
by cgsimp >> prove_is_mvn_uintegrable >> trace "DONE" >> tactic.failed

lemma g_final_diff_under_int_hd :
  can_differentiate_under_integrals g^.costs g^.nodes fdict (ID.str label.W_decode, [a^.nd, a^.nz]) :=
by cgsimp >> prove_is_mvn_uintegrable >> trace "DONE" >> tactic.failed

lemma g_final_diff_under_int_hdp :
  can_differentiate_under_integrals g^.costs g^.nodes fdict (ID.str label.W_decode_p, [a^.n_in, a^.nd]) :=
by cgsimp >> prove_is_mvn_uintegrable >> trace "DONE" >> tactic.failed



end proofs


end aevb
end certigrad
