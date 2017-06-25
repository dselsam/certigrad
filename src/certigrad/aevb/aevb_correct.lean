/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Proof of the end-to-end correctness theorem for the variational autoencoder: that
backpropagation on AEVB samples correct gradients for the naive variational autoencoder
we started with.
-/
import .util .graph .prog .grads_correct .transformations ..prove_model_ok ..backprop_correct

set_option profiler true

namespace certigrad
namespace aevb

open graph list tactic certigrad.tactic

#print "proving aevb_backprop_correct_for_naive_aevb..."

theorem aevb_backprop_correct_for_naive_aevb (a : arch) (ws : weights a) (x_data : T [a^.n_in, a^.n_x]) :
let g₀ : graph := naive_aevb a x_data in
let g_aevb : graph := reparam (integrate_kl g₀) in
let fdict : env := mk_input_dict ws x_data g₀ in
∀ (tgt : reference) (idx : ℕ) (H_at_idx : at_idx g₀^.targets idx tgt),
∇ (λ θ₀, E (graph.to_dist (λ m, ⟦sum_costs m g₀^.costs⟧) (env.insert tgt θ₀ fdict) g₀^.nodes) dvec.head) (env.get tgt fdict)
=
E (graph.to_dist (λ m, backprop g_aevb^.costs g_aevb^.nodes m g_aevb^.targets) fdict g_aevb^.nodes) (λ dict, dvec.get tgt.2 dict idx) :=

begin
whnf_target,
intros tgt idx H_at_idx,
simp only [@aevb_transformations_sound a ws x_data tgt idx H_at_idx],
apply backprop_correct_on_aevb,
rw [naive_aevb_as_graph] at H_at_idx,
rw [naive_aevb_as_graph],
exact H_at_idx
end

end aevb
end certigrad
