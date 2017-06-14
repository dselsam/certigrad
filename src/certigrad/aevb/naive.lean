/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Certigrad code for a naive variational autoencoder.
-/
import ..program ..prove_model_ok .util

namespace certigrad
namespace aevb

section program
open certigrad.program certigrad.program.statement certigrad.program.term certigrad.program.rterm list label

@[cgsimp] def prog_naive : Π (arch : aevb_arch) (x_data : T [arch^.n_in, arch^.n_x]), program | arch x_data :=

[
input batch_start     [],
param W_encode        [arch^.ne, arch^.n_in],
param W_encode_μ      [arch^.nz, arch^.ne],
param W_encode_log_σ₂ [arch^.nz, arch^.ne],
param W_decode        [arch^.nd, arch^.nz],
param W_decode_p      [arch^.n_in, arch^.nd],

assign x             $ get_col_range (const x_data) batch_start arch^.bs,
assign h_encode      $ softplus (gemm W_encode x),
assign μ             $ gemm W_encode_μ h_encode,
assign σ             $ sqrt (exp (gemm W_encode_log_σ₂ h_encode)),
sample z             $ mvn_iso μ σ,
assign encoding_loss $ mvn_iso_empirical_kl μ σ z,
assign p             $ sigmoid (gemm  W_decode_p (softplus (gemm W_decode z))),
assign decoding_loss $ bernoulli_neglogpdf p x,

cost encoding_loss,
cost decoding_loss
]

end program

@[cgsimp] def graph_naive : Π (arch : aevb_arch) (x_data : T [arch^.n_in, arch^.n_x]), graph
| arch x_data := program_to_graph (prog_naive arch x_data)

section nodes

open certigrad.det
open certigrad.det.cwise1
open certigrad.det.cwise2
open certigrad.det.special
open rand.op
open certigrad.tactic
open certigrad.label

lemma build_graph.unfold (arch : aevb_arch) (x_data : T [arch^.n_in, arch^.n_x]) :
graph_naive arch x_data =
graph.mk [⟨(0, [arch^.n_in, arch^.n_x]), [], operator.det $ op.const x_data⟩,
          ⟨(x, [arch^.n_in, arch^.bs]), [(0, [arch^.n_in, arch^.n_x]), (batch_start, [])], operator.det $ op.special $ get_col_range _ _ _⟩,
          ⟨(2, [arch^.ne, arch^.bs]), [(W_encode, [arch^.ne, arch^.n_in]), (x, [arch^.n_in, arch^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(h_encode, [arch^.ne, arch^.bs]), [(2, [arch^.ne, arch^.bs])], operator.det $ op.unary $ softplus⟩,
          ⟨(μ, [arch^.nz, arch^.bs]), [(W_encode_μ, [arch^.nz, arch^.ne]), (h_encode, [arch^.ne, arch^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(5, [arch^.nz, arch^.bs]), [(W_encode_log_σ₂, [arch^.nz, arch^.ne]), (h_encode, [arch^.ne, arch^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(6, [arch^.nz, arch^.bs]), [(5, [arch^.nz, arch^.bs])], operator.det $ op.unary exp⟩,
          ⟨(σ, [arch^.nz, arch^.bs]), [(6, [arch^.nz, arch^.bs])], operator.det $ op.unary sqrt⟩,
          ⟨(z, [arch^.nz, arch^.bs]), [(μ, [arch^.nz, arch^.bs]), (σ, [arch^.nz, arch^.bs])], operator.rand $ mvn_iso _⟩,
          ⟨(encoding_loss, []), [(μ, [arch^.nz, arch^.bs]), (σ, [arch^.nz, arch^.bs]), (z, [arch^.nz, arch^.bs])], operator.det $ op.mvn_iso_empirical_kl _⟩,
          ⟨(10, [arch^.nd, arch^.bs]), [(W_decode, [arch^.nd, arch^.nz]), (z, [arch^.nz, arch^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(11, [arch^.nd, arch^.bs]), [(10, [arch^.nd, arch^.bs])], operator.det $ op.unary $ softplus⟩,
          ⟨(12, [arch^.n_in, arch^.bs]), [(W_decode_p, [arch^.n_in, arch^.nd]), (11, [arch^.nd, arch^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(p, [arch^.n_in, arch^.bs]), [(12, [arch^.n_in, arch^.bs])], operator.det $ op.unary $ sigmoid⟩,
          ⟨(decoding_loss, []), [(p, [arch^.n_in, arch^.bs]), (x, [arch^.n_in, arch^.bs])], operator.det $ op.special $ bernoulli_neglogpdf _⟩]
         [encoding_loss, decoding_loss]
         [(W_encode, [arch.ne, arch.n_in]), (W_encode_μ, [arch.nz, arch.ne]), (W_encode_log_σ₂, [arch.nz, arch.ne]),
          (W_decode, [arch.nd, arch.nz]), (W_decode_p, [arch.n_in, arch.nd])]
         [(batch_start, []), (W_encode, [arch.ne, arch.n_in]), (W_encode_μ, [arch.nz, arch.ne]),
          (W_encode_log_σ₂, [arch.nz, arch.ne]), (W_decode, [arch.nd, arch.nz]), (W_decode_p, [arch.n_in, arch.nd])] := sorry
-- TODO(dhs): the following works (as of this writing) but is slow
-- by cgsimp

end nodes
end aevb
end certigrad
