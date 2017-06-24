/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Script to run AEVB on MNIST.
-/
import system.io ..program ..prove_model_ok .util .prog ..run_utils

namespace certigrad
namespace aevb

open io
/-
def n : ℕ := 55000
def bs : ℕ := 250
def nz : ℕ := 30
def nh : ℕ := 1000
def num_iters : ℕ := 500
def seed : ℕ := 100
-/

meta def train_aevb_on_mnist [io.interface] (a : arch) (num_iters seed : ℕ) (mnist_dir run_dir : string) : io unit := do
  put_str_ln ("reading mnist data from '" ++ mnist_dir ++ "' ..."),
  (train_data, train_labels) ← T.read_mnist run_dir,
  put_str_ln ("creating directory to store run data at '" ++ run_dir ++ "' ..."),
  mkdir run_dir,
  put_str_ln "building graph...",
  g ← return $ reparam (integrate_kl $ naive_aevb a train_data),
  put_str_ln "initializing the weights...",
  (ws, rng₁) ← return $ sample_initial_weights g.inputs (RNG.mk seed),
  put_str_ln "training...",
  num_batches ← return (a.n_x / a.bs),
  (θ, astate, rng₂) ← run.run_iters dir g p.n_x p.bs num_iters θ₀ optim.adam.init_state rng₁,
  put_str_ln "writing results...",
  tvec.write_all run_dir "params_" ".ssv" g^.targets θ',
  put_str_ln "(done)"

def mk_run_dir_name (dir : string) (a : arch) (num_iters seed : ℕ) : string :=
dir ++ "/run_bs=" ++ to_string a^.bs ++ "_nz=" ++ to_string a^.nz ++ "_nh=" ++ to_string a^.nd
    ++ "_iters=" ++ to_string num_iters ++ "_seed=" ++ to_string seed

-- TODO(dhs): confirm that this will run
meta def main [io.interface] : io unit :=
let a : arch := ⟨250, 60000, 784, 2, 500, 500⟩ in
let num_iters : ℕ := 1 in
let seed : ℕ := 0 in
let mnist_dir : string := "/home/dselsam/projects/mnist" in
let run_dir : string := mk_run_dir_name "/home/dselsam/projects/mnist/runs"
train_aevb_on_mnist a num_iters seed mnist_dir run_dir

run_cmd tactic.run_io @main

end aevb
end certigrad
