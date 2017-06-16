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
do applyc `pair_neq_of_neq₁,
   H ← intro `H,
   Hs ← injection H,
   match Hs with
   | [] := done
   | [H'] := contra_nats_eq H' <|>
             (do H''_ty ← mk_app `certigrad.label.label_eq_of_to_nat [H'],
                 note `H'' none H''_ty,
                 get_local `H'' >>= contra_nats_eq)
   | (x::y::xs) := fail "injection produced multiple hyps"
   end

example : (ID.str label.W_encode, [5]) ≠ (ID.str label.batch_start, []) := by prove_refs_neq
example : (ID.str label.W_encode, [5]) ≠ (ID.nat 5, [2, 3]) := by prove_refs_neq
example : (ID.nat 100, [5]) ≠ (ID.nat 11, []) := by prove_refs_neq
example : (ID.str label.W_encode, [5]) ≠ (ID.str label.batch_start, []) := by prove_refs_neq

end tactics

end certigrad
