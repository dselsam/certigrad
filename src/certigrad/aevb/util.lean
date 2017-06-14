/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Utilities for the AEVB model.
-/
import ..tensor ..graph ..env

namespace certigrad
namespace aevb

structure arch : Type := (bs n_x n_in nz ne nd : ℕ)

structure weights (a : arch) : Type :=
  (batch_start : ℝ)
  (W_encode : T [a^.ne, a^.n_in])
  (W_encode_μ W_encode_logσ₂ : T [a^.nz, a^.ne])
  (W_decode : T [a^.nd, a^.nz])
  (W_decode_p : T [a^.n_in, a^.nd])

section label
open certigrad.label
def mk_input_dict : Π {a : arch} (ws : weights a) (g : graph), env
| a ws g := env.insert_all [(batch_start, []), (W_encode, [a^.ne, a^.n_in]), (W_encode_μ, [a^.nz, a^.ne]), (W_encode_logσ₂, [a^.nz, a^.ne]),
                            (W_decode, [a^.nd, a^.nz]), (W_decode_p, [a^.n_in, a^.nd])]
                           ⟦ws^.batch_start, ws^.W_encode, ws^.W_encode_μ, ws^.W_encode_logσ₂, ws^.W_decode, ws^.W_decode_p⟧
end label

end aevb
end certigrad
