/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Certigrad code for a naive variational autoencoder.
-/
import ..program .util

namespace certigrad
namespace aevb

section program
open certigrad.program certigrad.program.statement certigrad.program.term certigrad.program.rterm list label

def naive_aevb (a : arch) (x_data : T [a^.n_in, a^.n_x]) : graph := program_to_graph
[
input x               [a^.n_in, a^.bs],
param W_encode₁       [a^.ne, a^.n_in],
param W_encode₂       [a^.ne, a^.ne],
param W_encode_μ      [a^.nz, a^.ne],
param W_encode_logσ₂  [a^.nz, a^.ne],
param W_decode₁       [a^.nd, a^.nz],
param W_decode₂       [a^.nd, a^.nd],
param W_decode_p      [a^.n_in, a^.nd],

assign h_encode      $ softplus (gemm W_encode₂ (softplus (gemm W_encode₁ x))),
assign μ             $ gemm W_encode_μ h_encode,
assign σ             $ sqrt (exp (gemm W_encode_logσ₂ h_encode)),
sample z             $ mvn μ σ,
assign encoding_loss $ mvn_empirical_kl μ σ z,
assign h_decode      $ softplus (gemm W_decode₂ (softplus (gemm W_decode₁ z))),
assign p             $ sigmoid (gemm  W_decode_p h_decode),
assign decoding_loss $ bernoulli_neglogpdf p x,

cost encoding_loss,
cost decoding_loss
]

end program

end aevb
end certigrad
