/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Proofs that integrating out the KL and reparametizing are sound when
applied to the naive variational encoder.
-/
import .util .naive ..prove_model_ok ..pre ..backprop_correct

set_option max_memory 4096

namespace certigrad
namespace aevb

open graph list tactic certigrad.tactic

section proof
parameters (a : arch) (ws : weights a) (x_data : T [a^.n_in, a^.n_x])
def g := reparam (integrate_kl $ graph_naive a x_data)
def fdict := mk_input_dict ws g

attribute [cgsimp] g fdict

private meta def prove_indep_hyps : tactic unit :=
do to_expr ```((g a x_data)^.targets ⊆ env.keys (fdict a ws x_data)) >>= assert `H_tgts_ss_inputs,
     solve1 cgsimp,
   to_expr ```(pdfs_exist_at (g a x_data)^.nodes (fdict a ws x_data)) >>= assert `H_pdfs_exist,
     solve1 cgsimp

private meta def prove_dep_hyps (tgt : expr) : tactic unit :=
do to_expr ```(well_formed_at (g a x_data)^.costs (g a x_data)^.nodes (fdict a ws x_data) %%tgt) >>= assert `H_wf,
     focus1 (constructor >> all_goals cgsimp), rotate 1,
   to_expr ```(grads_exist_at (g a x_data)^.nodes (fdict a ws x_data) %%tgt) >>= assert `H_gs_exist,
     solve1 (cgsimp),
   to_expr ```(is_gintegrable (λ m, ⟦compute_grad_slow (g a x_data)^.costs (g a x_data)^.nodes m %%tgt⟧) (fdict a ws x_data) (g a x_data)^.nodes dvec.head) >>= assert `H_gint,
     solve1 (cgsimp >> prove_is_mvn_integrable),
   to_expr ```(can_differentiate_under_integrals (g a x_data)^.costs (g a x_data)^.nodes (fdict a ws x_data) %%tgt) >>= assert `H_can_diff,
     solve1 (cgsimp >> prove_is_mvn_uintegrable)

private meta def forall_idxs (tac_base tac_step : tactic unit) : expr → tactic unit
| idx :=
tac_base <|>
(do cases idx [`_idx],
    solve1 tac_step,
    get_local `_idx >>= forall_idxs)

private meta def prove_aevb_base : tactic unit :=
do exfalso,
   H_at_idx ← get_local `H_at_idx,
   to_expr ```(list.at_idx_over %%H_at_idx dec_trivial) >>= exact

private meta def prove_aevb_step : tactic unit :=
do H_at_idx ← get_local `H_at_idx,
   mk_app `and.right [H_at_idx] >>= note `H_tgt_eq,
   H_tgt_eq_type ← get_local `H_tgt_eq >>= infer_type,
   s ← join_user_simp_lemmas true [`cgsimp],
   (H_tgt_eq_new_type, pr) ← simplify s H_tgt_eq_type {},
   get_local `H_tgt_eq >>= λ H_tgt_eq, replace_hyp H_tgt_eq H_tgt_eq_new_type pr,
   get_local `H_tgt_eq >>= subst,
   (tgt, new_tgt) ← match_eq H_tgt_eq_new_type,
   prove_dep_hyps new_tgt,
   to_expr ```(backprop_correct (fdict a ws x_data) (g a x_data)^.targets H_tgts_ss_inputs H_at_idx H_wf H_gs_exist H_pdfs_exist H_gint H_can_diff) >>= exact

meta def prove_aevb_ok : tactic unit :=
do -- introduce hypotheses
   [tgt, idx, H_at_idx] ← intros | fail "can't intro hyps",
   -- prove independent hyps once and for all
   prove_indep_hyps,
   -- repeated case-analysis on idx
   forall_idxs prove_aevb_base prove_aevb_step idx

lemma aevb_backprop_correct :
∀ (tgt : reference) (idx : ℕ) (H_at_idx : at_idx g^.targets idx tgt),
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ fdict) g^.nodes) dvec.head) (env.get tgt fdict)
=
E (graph.to_dist (λ m, backprop g^.costs g^.nodes m g^.targets) fdict g^.nodes) (λ dict, dvec.get tgt.2 dict idx) :=
by prove_aevb_ok

end proof
end aevb
end certigrad
