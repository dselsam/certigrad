/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

References.
-/
import .id .tensor library_dev_extras.util

namespace certigrad

@[reducible] def reference := ID × S

section tactics
open tactic

meta def prove_refs_neq : tactic unit :=
do applyc `pair_neq_of_neq₁, prove_ids_neq

end tactics

end certigrad
