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

theorem aevb_backprop_correct (a : arch) (ws : weights a) (x_data : T [a^.n_in, a^.n_x]) :
let g := reparam (integrate_kl $ graph_naive a x_data) in
let fdict := mk_input_dict ws g in
∀ (tgt : reference) (idx : ℕ) (H_at_idx : at_idx g^.targets idx tgt),
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) (env.insert tgt θ₀ fdict) g^.nodes) dvec.head) (env.get tgt fdict)
=
E (graph.to_dist (λ m, backprop g^.costs g^.nodes m g^.targets) fdict g^.nodes) (λ dict, dvec.get tgt.2 dict idx) :=
by do whnf_target,
      g ← to_expr ```(reparam (integrate_kl $ graph_naive a x_data)),
      fdict ← to_expr ```(mk_input_dict ws (reparam (integrate_kl $ graph_naive a x_data))),
      prove_model_ok g fdict


end aevb
end certigrad
