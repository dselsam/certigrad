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
graph.mk [⟨(ID.nat 0, [a^.n_in, a^.n_x]), [], operator.det $ op.const x_data⟩,
          ⟨(ID.str x, [a^.n_in, a^.bs]), [(ID.nat 0, [a^.n_in, a^.n_x]), (ID.str batch_start, [])], operator.det $ op.special $ get_col_range _ _ _⟩,
          ⟨(ID.nat 2, [a^.ne, a^.bs]), [(ID.str W_encode, [a^.ne, a^.n_in]), (ID.str x, [a^.n_in, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(ID.str h_encode, [a^.ne, a^.bs]), [(ID.nat 2, [a^.ne, a^.bs])], operator.det $ op.unary $ softplus⟩,
          ⟨(ID.str μ, [a^.nz, a^.bs]), [(ID.str W_encode_μ, [a^.nz, a^.ne]), (ID.str h_encode, [a^.ne, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(ID.nat 5, [a^.nz, a^.bs]), [(ID.str W_encode_logσ₂, [a^.nz, a^.ne]), (ID.str h_encode, [a^.ne, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(ID.nat 6, [a^.nz, a^.bs]), [(ID.nat 5, [a^.nz, a^.bs])], operator.det $ op.unary exp⟩,
          ⟨(ID.str σ, [a^.nz, a^.bs]), [(ID.nat 6, [a^.nz, a^.bs])], operator.det $ op.unary sqrt⟩,
          ⟨(ID.str z, [a^.nz, a^.bs]), [(ID.str μ, [a^.nz, a^.bs]), (ID.str σ, [a^.nz, a^.bs])], operator.rand $ mvn_iso _⟩,
          ⟨(ID.str encoding_loss, []), [(ID.str μ, [a^.nz, a^.bs]), (ID.str σ, [a^.nz, a^.bs]), (ID.str z, [a^.nz, a^.bs])], operator.det $ op.mvn_iso_empirical_kl _⟩,
          ⟨(ID.nat 10, [a^.nd, a^.bs]), [(ID.str W_decode, [a^.nd, a^.nz]), (ID.str z, [a^.nz, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(ID.nat 11, [a^.nd, a^.bs]), [(ID.nat 10, [a^.nd, a^.bs])], operator.det $ op.unary $ softplus⟩,
          ⟨(ID.nat 12, [a^.n_in, a^.bs]), [(ID.str W_decode_p, [a^.n_in, a^.nd]), (ID.nat 11, [a^.nd, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(ID.str p, [a^.n_in, a^.bs]), [(ID.nat 12, [a^.n_in, a^.bs])], operator.det $ op.unary $ sigmoid⟩,
          ⟨(ID.str decoding_loss, []), [(ID.str p, [a^.n_in, a^.bs]), (ID.str x, [a^.n_in, a^.bs])], operator.det $ op.special $ bernoulli_neglogpdf _⟩]
         [ID.str encoding_loss, ID.str decoding_loss]
         [(ID.str W_encode, [a^.ne, a^.n_in]), (ID.str W_encode_μ, [a^.nz, a^.ne]), (ID.str W_encode_logσ₂, [a^.nz, a^.ne]),
          (ID.str W_decode, [a^.nd, a^.nz]), (ID.str W_decode_p, [a^.n_in, a^.nd])]
         [(ID.str batch_start, []), (ID.str W_encode, [a^.ne, a^.n_in]), (ID.str W_encode_μ, [a^.nz, a^.ne]),
          (ID.str W_encode_logσ₂, [a^.nz, a^.ne]), (ID.str W_decode, [a^.nd, a^.nz]), (ID.str W_decode_p, [a^.n_in, a^.nd])]
-- TODO(dhs): the following works (as of this writing) but is slow
-- by cgsimp

end nodes
end aevb
end certigrad
