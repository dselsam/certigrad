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

open graph list tactic certigrad.tactic

private meta def prove_indep_hyps : tactic unit :=
do to_expr ```(g^.targets ⊆ env.keys fdict) >>= assert `H_tgts_ss_inputs,
     solve1 (dsimp >> cgsimp),
   to_expr ```(pdfs_exist_at g^.nodes fdict) >>= assert `H_pdfs_exist,
     solve1 (dsimp >> cgsimp)

private meta def prove_dep_hyps (tgt : expr) : tactic unit :=
do to_expr ```(well_formed_at g^.costs g^.nodes fdict %%tgt) >>= assert `H_wf,
     solve1 (dsimp >> constructor >> all_goals cgsimp),
   to_expr ```(grads_exist_at g^.nodes fdict %%tgt) >>= assert `H_gs_exist,
     solve1 (dsimp >> cgsimp),
   to_expr ```(is_gintegrable (λ m, ⟦compute_grad_slow g^.costs g^.nodes m %%tgt⟧) fdict g^.nodes dvec.head) >>= assert `H_gint,
     solve1 (dsimp >> cgsimp >> prove_is_mvn_integrable),
   to_expr ```(can_differentiate_under_integrals g^.costs g^.nodes fdict %%tgt) >>= assert `H_can_diff,
     solve1 (dsimp >> cgsimp >> prove_is_mvn_uintegrable)

private meta def forall_idxs (tac_base tac_step : tactic unit) : expr → tactic unit
| idx :=
tac_base <|>
(do cases idx [`_idx],
    solve1 tac_step,
    get_local `_idx >>= forall_idxs)

private meta def prove_aevb_base : tactic unit :=
do exfalso,
   H_at_idx ← get_local `H_at_idx,
   to_expr ```(list.at_idx_over H_at_idx dec_trivial) >>= exact

private meta def prove_aevb_step : tactic unit :=
do H_at_idx ← get_local `H_at_idx,
   H ← mk_app `and.right [H_at_idx],
   rewrite_core reducible tt tt occurrences.all ff H,
   H_type ← infer_type H,
   (tgt, new_tgt) ← match_eq H_type,
   prove_dep_hyps new_tgt,
   to_expr ```(backprop_correct fdict g^.targets H_tgts_ss_inputs H_at_idx H_wf H_gs_exist H_gint H_can_diff input_dict rfl) >>= exact

meta def prove_aevb_ok (tgt : expr) : tactic unit :=
do prove_indep_hyps,
   prove_dep_hyps tgt,
   H_at_idx ← get_local `H_at_idx,
   H ← mk_app `and.right [H_at_idx],
   rewrite_core reducible tt tt occurrences.all ff H,
   to_expr ```(backprop_correct fdict g^.targets H_tgts_ss_inputs H_at_idx H_wf H_gs_exist H_gint H_can_diff input_dict rfl) >>= exact

lemma aevb_backprop_correct (a : arch) (ws : weights a) (x_data : T [a^.n_in, a^.n_x]) :
let g : graph := reparam (integrate_kl $ graph_naive a x_data) in
let fdict : env := mk_input_dict ws g in
let init_dict : env := compute_init_dict g^.costs g^.nodes g^.targets in
∀ (tgt : reference) (idx : ℕ) (H_at_idx : at_idx g^.targets idx tgt),
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ fdict) g^.nodes) dvec.head) (env.get tgt fdict)
=
E (graph.to_dist (λ m, backprop g^.costs init_dict g^.nodes m g^.targets) fdict g^.nodes) (λ dict, dvec.get tgt.2 dict idx)
| tgt 0     H_at_idx := begin prove_aevb_ok (dnth g^.targets 0) end
| tgt 1     H_at_idx := begin prove_aevb_ok (dnth g^.targets 1) end
| tgt 2     H_at_idx := begin prove_aevb_ok (dnth g^.targets 2) end
| tgt 3     H_at_idx := begin prove_aevb_ok (dnth g^.targets 3) end
| tgt 4     H_at_idx := begin prove_aevb_ok (dnth g^.targets 4) end
| tgt (n+5) H_at_idx := false.rec _ (at_idx_over H_at_idx (by dec_triv))

#exit

end aevb
end certigrad
