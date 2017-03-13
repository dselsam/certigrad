/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Utilities for optimizing over stochastic computation graphs.
-/
import system.io system.time .tensor .tvec .optim .compute_grad .graph

namespace certigrad
open io

namespace T
meta constant read_from_file (shape : S) (s : string) [io.interface] : io (T shape)
meta constant write_to_file {shape : S} (x : T shape) (s : string) [io.interface] : io unit
end T

namespace tvec

meta def write_all_core [io.interface] (pfix sfix : string) : Π (names : list ID) (shapes : list S), dvec T shapes → io unit
| (name::names) (shape::shapes) (dvec.cons x xs) := do
  T.write_to_file x (pfix ++ to_string name ++ sfix),
  write_all_core names shapes xs
| _ _ _ := return ()

meta def write_all [io.interface] (dir pfix sfix : string) (refs : list reference) (xs : dvec T refs^.p2) : io unit := do
  mkdir dir,
  write_all_core (dir ++ "/" ++ pfix) sfix refs^.p1 refs^.p2 xs

end tvec

namespace run
open optim

@[reducible] def get_batch_start (batch_size batch_num : ℕ) : ℕ := batch_size * batch_num
@[reducible] def mk_initial_env (batch_size num_batches : ℕ) (targets : list reference) (θ : dvec T targets^.p2) : env :=
  env.insert (ID.str label.batch_start, []) (T.of_nat $ get_batch_start batch_size num_batches) (tvec.to_env targets θ)

def compute_costs (g : graph) (inputs : env) : state RNG (ℝ) :=
  let dist : sprog [[]] := graph.to_dist (λ env₀, ⟦sum_costs env₀ g^.costs⟧) inputs g^.nodes in do
  result ← dist^.to_rngprog,
  return (dvec.head result)

def compute_cost_epoch_core (g : graph) (batch_size : ℕ) (θ : dvec T g^.targets^.p2)
  : Π (batches_left : ℕ) (costs_so_far : ℝ), state RNG (ℝ)
| 0 cs := return cs

| (bl + 1) cs := do
    inputs ← return $ mk_initial_env batch_size bl g^.targets θ,
    c ← compute_costs g inputs,
    compute_cost_epoch_core bl (cs + c)

def compute_cost_epoch (g : graph) (batch_size : ℕ) (θ : dvec T g^.targets^.p2) (num_batches : ℕ) : state RNG (ℝ) := do
  total_ecost ← compute_cost_epoch_core g batch_size θ num_batches 0,
  return $ total_ecost / (T.of_nat $ batch_size * num_batches)

-- Assumes that "bstart" is an argument to the graph
def optimize_step (g : graph) (inputs : env) (astate : adam.state g^.targets^.p2) (θ : dvec T g^.targets^.p2) (init_dict : env) (batch_size : ℕ)
  : state RNG (dvec T g^.targets^.p2 × adam.state g^.targets^.p2) := do
    grads ← (graph.to_dist (λ env, backprop g^.costs init_dict g^.nodes env g^.targets) inputs g^.nodes)^.to_rngprog,
    return $ adam.step θ ((1 / T.of_nat batch_size) ⬝ grads) astate

def optimize_epoch_core (g : graph) (batch_size : ℕ)
  : Π (batches_left : ℕ) (astate : adam.state g^.targets^.p2) (θ : dvec T g^.targets^.p2) (init_dict : env), state RNG (dvec T g^.targets^.p2 × adam.state g^.targets^.p2)
| 0 astate θ init_dict := return (θ, astate)

| (bl + 1) astate θ init_dict := do
    inputs ← return $ mk_initial_env batch_size bl g^.targets θ,
    (θ_new, astate_new) ← optimize_step g inputs astate θ init_dict batch_size,
    optimize_epoch_core bl astate_new θ_new init_dict

def optimize_epoch (g : graph) (n_x batch_size : ℕ) (astate : adam.state g^.targets^.p2) (θ : dvec T g^.targets^.p2) (init_dict : env)
: state RNG (dvec T g^.targets^.p2 × ℝ × adam.state g^.targets^.p2) :=
  let num_batches : ℕ := n_x / batch_size in do
    (θ_new, astate_new) ← optimize_epoch_core g batch_size num_batches astate θ init_dict,
    epoch_cost ← compute_cost_epoch g batch_size θ_new num_batches,
    return (θ_new, epoch_cost, astate_new)

meta def run_epoch [io.interface] (g : graph) (n_x batch_size : ℕ) (astate : adam.state g^.targets^.p2) (θ : dvec T g^.targets^.p2) (rng : RNG) (init_dict : env)
  : io (dvec T g^.targets^.p2 × ℝ × adam.state g^.targets^.p2 × RNG) := do
      ((θ_new, epoch_costs, astate_new), rng_new) ← return $ optimize_epoch g n_x batch_size astate θ init_dict rng,
      return (θ_new, epoch_costs, astate_new, rng_new)

meta def run_iters_core [io.interface] (tval : time) (dir : string) (g : graph) (n_x batch_size : ℕ) (init_dict : env)
  : Π (num_iters : ℕ), dvec T g^.targets^.p2 → adam.state g^.targets^.p2 → RNG → io (dvec T g^.targets^.p2 × adam.state g^.targets^.p2 × RNG)
| 0 θ astate rng := return (θ, astate, rng)
| (t+1) θ astate rng := do ((θ', epoch_cost, astate', rng')) ← run_epoch g n_x batch_size astate θ rng init_dict,
--                           tvec.write_all (dir ++ "/iter" ++ to_string t) "params_" ".ssv" g^.targets θ',
                           tval' ← time.get,
                           put_str (to_string epoch_cost ++ ", " ++ time.sdiff tval' tval ++ "\n"),
                           run_iters_core t θ' astate' rng'

meta def run_iters [io.interface] (dir : string) (g : graph) (n_x batch_size : ℕ)
              (num_iters : ℕ) (θ : dvec T g^.targets^.p2) (astate : adam.state g^.targets^.p2) (rng : RNG)
  : io (dvec T g^.targets^.p2 × adam.state g^.targets^.p2 × RNG) := do
    init_dict ← return $ compute_init_dict g^.costs g^.nodes g^.targets,
    (epoch_cost, rng) ← return $ compute_cost_epoch g batch_size θ (n_x / batch_size) rng,
    tval ← time.get,
    put_str (to_string epoch_cost ++ ", 0\n"),
    run_iters_core tval dir g n_x batch_size init_dict num_iters θ astate rng

end run
end certigrad
