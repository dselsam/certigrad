/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Stochastic backpropagation.
-/
import library_dev_extras.util .tensor .tvec .graph

namespace certigrad
open list

def sum_costs (m : env) (costs : list ID) : ℝ := sumr (map (λ cost, env.get (cost, []) m) costs)

-- Note: we currently sum all costs in remaining nodes when we absorb at a PDF.
-- In sequential applications, it is crucial that only the costs that are topologogically downstream are summed.
-- Exercise for the reader: prove that such an optimization is sound, and update the implementation accordingly.

-- def sum_downstream_costs (nodes : list node) (costs : list ID) (tgt : reference) (m : env) : ℝ :=
--  sum (map (λ cost, DMap.get cost [] env) (filter (λ cost, IsDownstream cost tgt nodes) costs))

def sum_downstream_costs (nodes : list node) (costs : list ID) (tgt : reference) (m : env) : ℝ :=
  sum_costs m costs

def compute_grad_slow (costs : list ID) : Π (nodes : list node) (inputs : env) (tgt : reference), T tgt.2
| [] m tgt :=
  sumr (map (λ (cost : ID), if tgt = (cost, []) then 1 else 0) costs)

| (⟨ref, parents, operator.det op⟩::nodes) m tgt :=
  compute_grad_slow nodes m tgt
  + list.sumr (map (λ (idx : ℕ), op^.pb (env.get_ks parents m)
                                        (env.get ref m)
                                        (compute_grad_slow nodes m ref)
                                        idx
                                        tgt.2)
                    (filter (λ idx, tgt = dnth parents idx) (riota $ length parents)))

| (⟨ref, parents, operator.rand op⟩::nodes) m tgt :=
  compute_grad_slow nodes m tgt
  + list.sumr (map (λ (idx : ℕ), sum_downstream_costs nodes costs ref m ⬝ op^.glogpdf (env.get_ks parents m) (env.get ref m) idx tgt.2)
                   (filter (λ idx, tgt = dnth parents idx) (riota $ length parents)))

def compute_grad_step (costs : list ID) (callback : list node → Π (tgt : reference), T tgt.2) : Π (nodes : list node) (inputs : env) (tgt : reference), T tgt.2
| [] m tgt :=
  sumr₁ (map (λ (cost : ID), if tgt = (cost, []) then T.one _ else T.zero _) costs)

| (⟨ref, parents, operator.det op⟩::nodes) m tgt :=
  sumrd (callback nodes tgt)
        (map (λ (idx : ℕ), op^.pb (env.get_ks parents m)
                                  (env.get ref m)
                                  (callback nodes ref)
                                  idx
                                  tgt.2)
             (filter (λ idx, tgt = dnth parents idx) (riota $ length parents)))

| (⟨ref, parents, operator.rand op⟩::nodes) m tgt :=
  sumrd (callback nodes tgt)
        (map (λ (idx : ℕ), sum_downstream_costs nodes costs ref m ⬝ op^.glogpdf (env.get_ks parents m) (env.get ref m) idx tgt.2)
             (filter (λ idx, tgt = dnth parents idx) (riota $ length parents)))

def compute_init_dict (costs : list ID) : Π (nodes : list node) (tgts : list reference), env
| [] tgts :=
foldr (λ (tgt : reference) (dict : env),
          env.insert tgt
                      (compute_grad_step costs (λ (nodes : list node) (tgt' : reference), T.error "backprop-end") [] env.mk tgt)
                     dict)
      env.mk
      tgts

| (n :: nodes) tgts := compute_init_dict nodes (n^.ref :: tgts)

def backprop_core_helper (costs : list ID) (init_dict : env) : Π (nodes : list node) (dict : env) (tgts : list reference), env
| [] m tgts  := init_dict

| (n :: nodes) m tgts :=

let old_dict := backprop_core_helper nodes m (n^.ref :: tgts) in
foldr (λ (tgt : reference) (dict : env),
          env.insert tgt
                      (compute_grad_step costs (λ (nodes' : list node) (tgt' : reference), env.get tgt' old_dict)
                                         (n::nodes) m tgt)
                     dict)
      env.mk
      tgts

def backprop_core (costs : list ID) (nodes : list node) (dict : env) (tgts : list reference) : env :=
backprop_core_helper costs (compute_init_dict costs nodes tgts) nodes dict tgts

def backprop (costs : list ID) (nodes : list node) (inputs : env) (tgts : list reference) : dvec T tgts^.p2 :=
  let dict := backprop_core costs nodes inputs tgts in tvec.from_env tgts dict

end certigrad
