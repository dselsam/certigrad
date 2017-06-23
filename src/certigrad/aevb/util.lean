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
  (W_encode₁ : T [a^.ne, a^.n_in])
  (W_encode₂ : T [a^.ne, a^.ne])
  (W_encode_μ W_encode_logσ₂ : T [a^.nz, a^.ne])
  (W_decode₁ : T [a^.nd, a^.nz])
  (W_decode₂ : T [a^.nd, a^.nd])
  (W_decode_p : T [a^.n_in, a^.nd])

section label
open certigrad.label
@[cgsimp] def mk_input_dict : Π {a : arch} (ws : weights a) (g : graph), env
| a ws g := env.insert_all [(ID.str batch_start, []),
                            (ID.str W_encode₁, [a^.ne, a^.n_in]),
                            (ID.str W_encode₂, [a^.ne, a^.ne]),
                            (ID.str W_encode_μ, [a^.nz, a^.ne]),
                            (ID.str W_encode_logσ₂, [a^.nz, a^.ne]),
                            (ID.str W_decode₁, [a^.nd, a^.nz]),
                            (ID.str W_decode₂, [a^.nd, a^.nd]),
                            (ID.str W_decode_p, [a^.n_in, a^.nd])]
                           ⟦ws^.batch_start, ws^.W_encode₁, ws^.W_encode₂, ws^.W_encode_μ, ws^.W_encode_logσ₂,
                            ws^.W_decode₁, ws^.W_decode₂, ws^.W_decode_p⟧
end label

end aevb
end certigrad
