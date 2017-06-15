/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Certigrad code for a naive variational autoencoder.
-/
import ..program ..prove_model_ok .util

namespace certigrad
namespace aevb
/-
section program
open certigrad.program certigrad.program.statement certigrad.program.term certigrad.program.rterm list label

@[cgsimp] def prog_naive : Π (a : arch) (x_data : T [a^.n_in, a^.n_x]), program | a x_data :=

[
input batch_start     [],
param W_encode        [a^.ne, a^.n_in],
param W_encode_μ      [a^.nz, a^.ne],
param W_encode_logσ₂  [a^.nz, a^.ne],
param W_decode        [a^.nd, a^.nz],
param W_decode_p      [a^.n_in, a^.nd],

assign x             $ get_col_range (const x_data) batch_start a^.bs,
assign h_encode      $ softplus (gemm W_encode x),
assign μ             $ gemm W_encode_μ h_encode,
assign σ             $ sqrt (exp (gemm W_encode_logσ₂ h_encode)),
sample z             $ mvn_iso μ σ,
assign encoding_loss $ mvn_iso_empirical_kl μ σ z,
assign p             $ sigmoid (gemm  W_decode_p (softplus (gemm W_decode z))),
assign decoding_loss $ bernoulli_neglogpdf p x,

cost encoding_loss,
cost decoding_loss
]

end program

@[cgsimp] def graph_naive : Π (a : arch) (x_data : T [a^.n_in, a^.n_x]), graph
| a x_data := program_to_graph (prog_naive a x_data)
-/
section nodes

open det det.cwise1 det.cwise2 det.special rand.op label certigrad.tactic

@[cgsimp] def graph_naive : Π (a : arch) (x_data : T [a^.n_in, a^.n_x]), graph
| a x_data :=
graph.mk [⟨(0, [a^.n_in, a^.n_x]), [], operator.det $ op.const x_data⟩,
          ⟨(x, [a^.n_in, a^.bs]), [(0, [a^.n_in, a^.n_x]), (batch_start, [])], operator.det $ op.special $ get_col_range _ _ _⟩,
          ⟨(2, [a^.ne, a^.bs]), [(W_encode, [a^.ne, a^.n_in]), (x, [a^.n_in, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(h_encode, [a^.ne, a^.bs]), [(2, [a^.ne, a^.bs])], operator.det $ op.unary $ softplus⟩,
          ⟨(μ, [a^.nz, a^.bs]), [(W_encode_μ, [a^.nz, a^.ne]), (h_encode, [a^.ne, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(5, [a^.nz, a^.bs]), [(W_encode_logσ₂, [a^.nz, a^.ne]), (h_encode, [a^.ne, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(6, [a^.nz, a^.bs]), [(5, [a^.nz, a^.bs])], operator.det $ op.unary exp⟩,
          ⟨(σ, [a^.nz, a^.bs]), [(6, [a^.nz, a^.bs])], operator.det $ op.unary sqrt⟩,
          ⟨(z, [a^.nz, a^.bs]), [(μ, [a^.nz, a^.bs]), (σ, [a^.nz, a^.bs])], operator.rand $ mvn_iso _⟩,
          ⟨(encoding_loss, []), [(μ, [a^.nz, a^.bs]), (σ, [a^.nz, a^.bs]), (z, [a^.nz, a^.bs])], operator.det $ op.mvn_iso_empirical_kl _⟩,
          ⟨(10, [a^.nd, a^.bs]), [(W_decode, [a^.nd, a^.nz]), (z, [a^.nz, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(11, [a^.nd, a^.bs]), [(10, [a^.nd, a^.bs])], operator.det $ op.unary $ softplus⟩,
          ⟨(12, [a^.n_in, a^.bs]), [(W_decode_p, [a^.n_in, a^.nd]), (11, [a^.nd, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(p, [a^.n_in, a^.bs]), [(12, [a^.n_in, a^.bs])], operator.det $ op.unary $ sigmoid⟩,
          ⟨(decoding_loss, []), [(p, [a^.n_in, a^.bs]), (x, [a^.n_in, a^.bs])], operator.det $ op.special $ bernoulli_neglogpdf _⟩]
         [encoding_loss, decoding_loss]
         [(W_encode, [a^.ne, a^.n_in]), (W_encode_μ, [a^.nz, a^.ne]), (W_encode_logσ₂, [a^.nz, a^.ne]),
          (W_decode, [a^.nd, a^.nz]), (W_decode_p, [a^.n_in, a^.nd])]
         [(batch_start, []), (W_encode, [a^.ne, a^.n_in]), (W_encode_μ, [a^.nz, a^.ne]),
          (W_encode_logσ₂, [a^.nz, a^.ne]), (W_decode, [a^.nd, a^.nz]), (W_decode_p, [a^.n_in, a^.nd])]
-- TODO(dhs): the following works (as of this writing) but is slow
-- by cgsimp

end nodes
end aevb
end certigrad
