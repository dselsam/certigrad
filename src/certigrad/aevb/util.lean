/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Utilities for the AEVB model.
-/
import ..tensor

namespace certigrad
namespace aevb

structure aevb_arch : Type := (bs n_x n_in nz ne nd : ℕ)

def weights (arch : aevb_arch) : Type :=
  dvec T [[], [arch^.ne, arch^.n_in], [arch^.nz, arch^.ne], [arch^.nz, arch^.ne], [arch^.nd, arch^.nz], [arch^.n_in, arch^.nd]]

def mk_weights (arch : aevb_arch)
               (bstart : ℝ)
               (he : T [arch^.ne, arch^.n_in])
               (he_μ he_logσ₂: T [arch^.nz, arch^.ne])
               (hd : T [arch^.nd, arch^.nz])
               (hd_γ : T [arch^.n_in, arch^.nd]) : weights arch := ⟦bstart, he, he_μ, he_logσ₂, hd, hd_γ⟧

end aevb
end certigrad
