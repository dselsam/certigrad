/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

The actual graph produced by the naive variational auto-encoder code in aevb/prog.lean.

Note: we include this file as an optimization, to avoid repeatedly simplifying the
program into the graph.
-/
import ..program ..prove_model_ok .util .prog

namespace certigrad
namespace aevb

section nodes

open det rand.op label tactic certigrad.tactic

def graph_naive : Π (a : arch) (x_data : T [a^.n_in, a^.n_x]), graph
| a x_data :=
graph.mk [⟨(ID.nat 0, [a^.ne, a^.bs]), [(ID.str W_encode₁, [a^.ne, a^.n_in]), (ID.str x, [a^.n_in, a^.bs])], operator.det $ ops.gemm _ _ _⟩,
          ⟨(ID.nat 1, [a^.ne, a^.bs]), [(ID.nat 0, [a^.ne, a^.bs])], operator.det $ ops.softplus _⟩,
          ⟨(ID.nat 2, [a^.ne, a^.bs]), [(ID.str W_encode₂, [a^.ne, a^.ne]), (ID.nat 1, [a^.ne, a^.bs])], operator.det $ ops.gemm _ _ _⟩,
          ⟨(ID.str h_encode, [a^.ne, a^.bs]), [(ID.nat 2, [a^.ne, a^.bs])], operator.det $ ops.softplus _⟩,
          ⟨(ID.str μ, [a^.nz, a^.bs]), [(ID.str W_encode_μ, [a^.nz, a^.ne]), (ID.str h_encode, [a^.ne, a^.bs])], operator.det $ ops.gemm _ _ _⟩,
          ⟨(ID.nat 5, [a^.nz, a^.bs]), [(ID.str W_encode_logσ₂, [a^.nz, a^.ne]), (ID.str h_encode, [a^.ne, a^.bs])], operator.det $ ops.gemm _ _ _⟩,
          ⟨(ID.nat 6, [a^.nz, a^.bs]), [(ID.nat 5, [a^.nz, a^.bs])], operator.det $ ops.exp _⟩,
          ⟨(ID.str σ, [a^.nz, a^.bs]), [(ID.nat 6, [a^.nz, a^.bs])], operator.det $ ops.sqrt _⟩,
          ⟨(ID.str z, [a^.nz, a^.bs]), [(ID.str μ, [a^.nz, a^.bs]), (ID.str σ, [a^.nz, a^.bs])], operator.rand $ mvn_iso _⟩,
          ⟨(ID.str encoding_loss, []), [(ID.str μ, [a^.nz, a^.bs]), (ID.str σ, [a^.nz, a^.bs]), (ID.str z, [a^.nz, a^.bs])], operator.det $ op.mvn_iso_empirical_kl _⟩,
          ⟨(ID.nat 10, [a^.nd, a^.bs]), [(ID.str W_decode₁, [a^.nd, a^.nz]), (ID.str z, [a^.nz, a^.bs])], operator.det $ ops.gemm _ _ _⟩,
          ⟨(ID.nat 11, [a^.nd, a^.bs]), [(ID.nat 10, [a^.nd, a^.bs])], operator.det $ ops.softplus _⟩,
          ⟨(ID.nat 12, [a^.nd, a^.bs]), [(ID.str W_decode₂, [a^.nd, a^.nd]), (ID.nat 11, [a^.nd, a^.bs])], operator.det $ ops.gemm _ _ _⟩,
          ⟨(ID.str h_decode, [a^.nd, a^.bs]), [(ID.nat 12, [a^.nd, a^.bs])], operator.det $ ops.softplus _⟩,
          ⟨(ID.nat 14, [a^.n_in, a^.bs]), [(ID.str W_decode_p, [a^.n_in, a^.nd]), (ID.str h_decode, [a^.nd, a^.bs])], operator.det $ ops.gemm _ _ _⟩,
          ⟨(ID.str p, [a^.n_in, a^.bs]), [(ID.nat 14, [a^.n_in, a^.bs])], operator.det $ ops.sigmoid _⟩,
          ⟨(ID.str decoding_loss, []), [(ID.str p, [a^.n_in, a^.bs]), (ID.str x, [a^.n_in, a^.bs])], operator.det $ ops.bernoulli_neglogpdf _⟩]
         [ID.str encoding_loss, ID.str decoding_loss]
         [(ID.str W_encode₁, [a^.ne, a^.n_in]), (ID.str W_encode₂, [a^.ne, a^.ne]), (ID.str W_encode_μ, [a^.nz, a^.ne]), (ID.str W_encode_logσ₂, [a^.nz, a^.ne]),
          (ID.str W_decode₁, [a^.nd, a^.nz]), (ID.str W_decode₂, [a^.nd, a^.nd]), (ID.str W_decode_p, [a^.n_in, a^.nd])]
         [(ID.str x, [a^.n_in, a^.bs]),
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
