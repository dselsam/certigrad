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

meta def load_mnist_dataset [io.interface] (mnist_dir : string) (a : arch) : io (T [a^.n_in, a^.n_x] × T [a^.n_x]) :=
if H : 60000 = a^.n_x ∧ 784 = a^.n_in
then do (x, y) ← T.read_mnist mnist_dir,
        return $ eq.rec_on H^.left (eq.rec_on H^.right (x^.transpose, y))
else io.fail "architecture not compatible with mnist"

meta def train_aevb_on_mnist [io.interface] (a : arch) (num_iters seed : ℕ) (mnist_dir run_dir : string) : io unit := do
  put_str_ln ("reading mnist data from '" ++ mnist_dir ++ "' ..."),
  (train_data, train_labels) ← load_mnist_dataset mnist_dir a,
  x_data ← return $ T.get_col_range a^.n_x train_data 0,
  put_str_ln ("creating directory to store run data at '" ++ run_dir ++ "' ..."),
  mkdir run_dir,
  put_str_ln "building graph...",
  g ← return $ reparam (integrate_kl $ naive_aevb a x_data),
  put_str_ln "initializing the weights...",
  (ws, rng₁) ← return $ sample_initial_weights g^.targets (RNG.mk seed),
  put_str_ln "training...",
  num_batches ← return (a.n_x / a.bs),
  (θ, astate, rng₂) ← run.run_iters run_dir g train_data a^.bs num_iters ws optim.adam.init_state rng₁,
  put_str_ln "writing results...",
  tvec.write_all run_dir "params_" ".ssv" g^.targets θ,
  put_str_ln "(done)"

def mk_run_dir_name (dir : string) (a : arch) (num_iters seed : ℕ) : string :=
dir ++ "/run_bs=" ++ to_string a^.bs ++ "_nz=" ++ to_string a^.nz ++ "_nh=" ++ to_string a^.nd
    ++ "_iters=" ++ to_string num_iters ++ "_seed=" ++ to_string seed


------------------------------------
-- Script to train an AEVB on MNIST.
------------------------------------
-- 1. Create a directory 'mnist_dir'
-- 2. Download, uncompress, and put in 'mnist_dir':
--      http://yann.lecun.com/exdb/mnist/train-images-idx3-ubyte.gz
--      http://yann.lecun.com/exdb/mnist/train-labels-idx1-ubyte.gz
-- 3. Create a directory for 'run_dir' to store data from different runs.
-- 4. Change 'mnist_dir' and 'run_dir' below accordingly.
-- 5. Uncomment the 'run_cmd tactic.run_io @main' command below to run it.

--set_option profiler true

meta def train_core [io.interface] (a : arch) (num_iters seed : ℕ) : io unit :=
let mnist_dir : string := "/home/dselsam/projects/mnist" in
let run_dir : string := mk_run_dir_name "/home/dselsam/projects/mnist/runs" a num_iters seed in
train_aevb_on_mnist a num_iters seed mnist_dir run_dir

meta def main [io.interface] : io unit :=
let a : arch := {bs := 250, n_x := 60000, n_in := 784, nz := 30, ne := 1000, nd := 1000} in
let num_iters : ℕ := 1000 in
let seed : ℕ := 100 in
train_core a num_iters seed

--run_cmd tactic.run_io @main

end aevb
end certigrad
