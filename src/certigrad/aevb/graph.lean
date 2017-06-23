/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Certigrad code for a naive variational autoencoder.
-/
import ..program ..prove_model_ok .util .prog

namespace certigrad
namespace aevb

section nodes

open det det.cwise1 det.cwise2 det.special rand.op label tactic certigrad.tactic

def graph_naive : Π (a : arch) (x_data : T [a^.n_in, a^.n_x]), graph
| a x_data :=
graph.mk [⟨(ID.nat 0, [a^.n_in, a^.n_x]), [], operator.det $ op.const x_data⟩,
          ⟨(ID.str x, [a^.n_in, a^.bs]), [(ID.nat 0, [a^.n_in, a^.n_x]), (ID.str batch_start, [])], operator.det $ op.special $ get_col_range _ _ _⟩,
          ⟨(ID.nat 2, [a^.ne, a^.bs]), [(ID.str W_encode₁, [a^.ne, a^.n_in]), (ID.str x, [a^.n_in, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(ID.nat 3, [a^.ne, a^.bs]), [(ID.nat 2, [a^.ne, a^.bs])], operator.det $ op.unary $ softplus⟩,
          ⟨(ID.nat 4, [a^.ne, a^.bs]), [(ID.str W_encode₂, [a^.ne, a^.ne]), (ID.nat 3, [a^.ne, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(ID.str h_encode, [a^.ne, a^.bs]), [(ID.nat 4, [a^.ne, a^.bs])], operator.det $ op.unary $ softplus⟩,
          ⟨(ID.str μ, [a^.nz, a^.bs]), [(ID.str W_encode_μ, [a^.nz, a^.ne]), (ID.str h_encode, [a^.ne, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(ID.nat 7, [a^.nz, a^.bs]), [(ID.str W_encode_logσ₂, [a^.nz, a^.ne]), (ID.str h_encode, [a^.ne, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(ID.nat 8, [a^.nz, a^.bs]), [(ID.nat 7, [a^.nz, a^.bs])], operator.det $ op.unary exp⟩,
          ⟨(ID.str σ, [a^.nz, a^.bs]), [(ID.nat 8, [a^.nz, a^.bs])], operator.det $ op.unary sqrt⟩,
          ⟨(ID.str z, [a^.nz, a^.bs]), [(ID.str μ, [a^.nz, a^.bs]), (ID.str σ, [a^.nz, a^.bs])], operator.rand $ mvn_iso _⟩,
          ⟨(ID.str encoding_loss, []), [(ID.str μ, [a^.nz, a^.bs]), (ID.str σ, [a^.nz, a^.bs]), (ID.str z, [a^.nz, a^.bs])], operator.det $ op.mvn_iso_empirical_kl _⟩,
          ⟨(ID.nat 12, [a^.nd, a^.bs]), [(ID.str W_decode₁, [a^.nd, a^.nz]), (ID.str z, [a^.nz, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(ID.nat 13, [a^.nd, a^.bs]), [(ID.nat 12, [a^.nd, a^.bs])], operator.det $ op.unary $ softplus⟩,
          ⟨(ID.nat 14, [a^.nd, a^.bs]), [(ID.str W_decode₂, [a^.nd, a^.nd]), (ID.nat 13, [a^.nd, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(ID.nat 15, [a^.nd, a^.bs]), [(ID.nat 14, [a^.nd, a^.bs])], operator.det $ op.unary $ softplus⟩,
          ⟨(ID.nat 16, [a^.n_in, a^.bs]), [(ID.str W_decode_p, [a^.n_in, a^.nd]), (ID.nat 15, [a^.nd, a^.bs])], operator.det $ op.special $ gemm _ _ _⟩,
          ⟨(ID.str p, [a^.n_in, a^.bs]), [(ID.nat 16, [a^.n_in, a^.bs])], operator.det $ op.unary $ sigmoid⟩,
          ⟨(ID.str decoding_loss, []), [(ID.str p, [a^.n_in, a^.bs]), (ID.str x, [a^.n_in, a^.bs])], operator.det $ op.special $ bernoulli_neglogpdf _⟩]
         [ID.str encoding_loss, ID.str decoding_loss]
         [(ID.str W_encode₁, [a^.ne, a^.n_in]), (ID.str W_encode₂, [a^.ne, a^.ne]), (ID.str W_encode_μ, [a^.nz, a^.ne]), (ID.str W_encode_logσ₂, [a^.nz, a^.ne]),
          (ID.str W_decode₁, [a^.nd, a^.nz]), (ID.str W_decode₂, [a^.nd, a^.nd]), (ID.str W_decode_p, [a^.n_in, a^.nd])]
         [(ID.str batch_start, []),
          (ID.str W_encode₁, [a^.ne, a^.n_in]), (ID.str W_encode₂, [a^.ne, a^.ne]), (ID.str W_encode_μ, [a^.nz, a^.ne]), (ID.str W_encode_logσ₂, [a^.nz, a^.ne]),
          (ID.str W_decode₁, [a^.nd, a^.nz]), (ID.str W_decode₂, [a^.nd, a^.nd]), (ID.str W_decode_p, [a^.n_in, a^.nd])]

attribute [cgsimp] graph_naive

open tactic certigrad.tactic

#print "proving naive_aevb_as_graph..."
@[cgsimp] lemma naive_aevb_as_graph (a : arch) (x_data : T [a^.n_in, a^.n_x]) : naive_aevb a x_data = graph_naive a x_data :=
by { dunfold naive_aevb, cgsimp, dcgsimp, cgsimp, reflexivity }

end nodes

end aevb
end certigrad
