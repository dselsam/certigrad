/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Proofs that integrating out the KL and reparametizing are sound when
applied to the naive variational encoder.
-/
import .util .naive ..prove_model_ok ..pre ..backprop_correct

set_option max_memory 2048

namespace certigrad
namespace aevb

set_option profiler true
open graph list tactic certigrad.tactic

meta def prove_for_tgt : tactic unit :=
do trace "prove_for_tgt start...",
   whnf_target,

/-
   H_at_idx ← get_local `H_at_idx,
   mk_app `and.right [H_at_idx] >>= note `H_tgt_eq,
   H_tgt_eq_type ← get_local `H_tgt_eq >>= infer_type,
   s ← join_user_simp_lemmas true [`cgsimp],
   (H_tgt_eq_new_type, pr) ← simplify s H_tgt_eq_type {},
   get_local `H_tgt_eq >>= λ H_tgt_eq, replace_hyp H_tgt_eq H_tgt_eq_new_type pr,
   get_local `H_tgt_eq >>= subst,
-/
   applyc `certigrad.backprop_correct,
   trace "targets subset inputs...",
     solve1 cgsimp,
   trace "at_idx...",
     solve1 (applyc `and.intro >> dec_triv >> reflexivity),
   trace "well_formed_at...",
     solve1 (constructor >> all_goals cgsimp),
   trace "grads_exist_at...",
     solve1 (cgsimp),
   trace "pdfs_exist_at...",
     solve1 cgsimp,
   trace "is_gintegrable...",
     solve1 (cgsimp >> prove_is_mvn_integrable),
   trace "can_diff_under_ints...",
     solve1 (cgsimp >> prove_is_mvn_uintegrable),
   trace "prove_for_tgt done"

section params

parameters (a : arch) (ws : weights a) (x_data : T [a^.n_in, a^.n_x])
def g : graph := reparam (integrate_kl $ graph_naive a x_data)
def fdict : env := mk_input_dict ws g

attribute [cgsimp] g fdict

lemma aevb_backprop_correct_W_encode :
let idx := 0 in
let tgt := (ID.str label.W_encode, [a^.ne, a^.n_in]) in
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ fdict) g^.nodes) dvec.head) (env.get tgt fdict)
=
E (graph.to_dist (λ m, backprop g^.costs g^.nodes m g^.targets) fdict g^.nodes) (λ dict, dvec.get tgt.2 dict idx) :=
by prove_for_tgt

lemma aevb_backprop_correct_W_encode_μ :
let idx := 1 in
let tgt := (ID.str label.W_encode_μ, [a^.nz, a^.ne]) in
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ fdict) g^.nodes) dvec.head) (env.get tgt fdict)
=
E (graph.to_dist (λ m, backprop g^.costs g^.nodes m g^.targets) fdict g^.nodes) (λ dict, dvec.get tgt.2 dict idx) :=
by prove_for_tgt

lemma aevb_backprop_correct_W_encode_logσ₂ :
let idx := 2 in
let tgt := (ID.str label.W_encode_logσ₂, [a^.nz, a^.ne]) in
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ fdict) g^.nodes) dvec.head) (env.get tgt fdict)
=
E (graph.to_dist (λ m, backprop g^.costs g^.nodes m g^.targets) fdict g^.nodes) (λ dict, dvec.get tgt.2 dict idx) :=
by prove_for_tgt

lemma aevb_backprop_correct_W_decode :
let idx := 3 in
let tgt := (ID.str label.W_decode, [a^.nd, a^.nz]) in
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ fdict) g^.nodes) dvec.head) (env.get tgt fdict)
=
E (graph.to_dist (λ m, backprop g^.costs g^.nodes m g^.targets) fdict g^.nodes) (λ dict, dvec.get tgt.2 dict idx) :=
by prove_for_tgt

lemma aevb_backprop_correct_W_decode_p :
let idx := 4 in
let tgt := (ID.str label.W_decode_p, [a^.n_in, a^.nd]) in
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ fdict) g^.nodes) dvec.head) (env.get tgt fdict)
=
E (graph.to_dist (λ m, backprop g^.costs g^.nodes m g^.targets) fdict g^.nodes) (λ dict, dvec.get tgt.2 dict idx) :=
by prove_for_tgt

theorem aevb_backprop_correct :
∀ (tgt : reference) (idx : ℕ) (H_at_idx : at_idx g^.targets idx tgt),
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ fdict) g^.nodes) dvec.head) (env.get tgt fdict)
=
E (graph.to_dist (λ m, backprop g^.costs g^.nodes m g^.targets) fdict g^.nodes) (λ dict, dvec.get tgt.2 dict idx)
| tgt 0     H_at_idx := begin note H := and.right H_at_idx, subst H, apply aevb_backprop_correct_W_encode end
| tgt 1     H_at_idx := begin note H := and.right H_at_idx, subst H, apply aevb_backprop_correct_W_encode_μ end
| tgt 2     H_at_idx := begin note H := and.right H_at_idx, subst H, apply aevb_backprop_correct_W_encode_logσ₂ end
| tgt 3     H_at_idx := begin note H := and.right H_at_idx, subst H, apply aevb_backprop_correct_W_decode end
| tgt 4     H_at_idx := begin note H := and.right H_at_idx, subst H, apply aevb_backprop_correct_W_decode_p end
| tgt (n+5) H_at_idx := false.rec _ $ list.at_idx_over H_at_idx dec_trivial

end params
end aevb
end certigrad
