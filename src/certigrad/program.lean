/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

A term language for conveniently constructing stochastic computation graphs.
-/
import .tensor .graph .tactics .ops data.hash_map

namespace certigrad
namespace program
open list

inductive unary_op : Type
| neg : unary_op, exp, log, sqrt, softplus, sigmoid

inductive binary_op : Type
| add, sub, mul, div

inductive term : Type
| unary : unary_op → term → term
| binary : binary_op → term → term → term
| sum : term → term
| scale : ℝ → term → term
| gemm : term → term → term
| mvn_iso_kl : term → term → term
| mvn_iso_empirical_kl : term → term → term → term
| bernoulli_neglogpdf : term → term → term
| id : label → term

instance : has_neg term := ⟨term.unary unary_op.neg⟩
instance : has_smul ℝ term := ⟨term.scale⟩
instance : has_add term := ⟨term.binary binary_op.add⟩
instance : has_sub term := ⟨term.binary binary_op.sub⟩
instance : has_mul term := ⟨term.binary binary_op.mul⟩
instance : has_div term := ⟨term.binary binary_op.div⟩

instance coe_id : has_coe label term := ⟨term.id⟩

def exp : term → term := term.unary unary_op.exp
def log : term → term := term.unary unary_op.log
def sqrt : term → term := term.unary unary_op.sqrt
def softplus : term → term := term.unary unary_op.softplus
def sigmoid : term → term := term.unary unary_op.sigmoid

inductive rterm : Type
| mvn_iso : term → term → rterm
| mvn_iso_std : S → rterm

inductive statement : Type
| param : label → S → statement
| input : label → S → statement
| cost : label → statement
| assign : label → term → statement
| sample : label → rterm → statement

structure state : Type :=
  (next_id : ℕ) (shapes : hash_map label (λ x, S))
  (nodes : list node) (costs : list ID) (targets inputs : list reference)

def empty_state : state := ⟨0, mk_hash_map (λ (x : label), x^.to_nat), [], [], [], []⟩

def unary_to_op (shape : S) : unary_op → det.op [shape] shape
| unary_op.neg      := ops.neg shape
| unary_op.exp      := ops.exp shape
| unary_op.log      := ops.log shape
| unary_op.sqrt     := ops.sqrt shape
| unary_op.softplus := ops.softplus shape
| unary_op.sigmoid  := ops.sigmoid shape

def binary_to_cwise2 (shape : S) : binary_op → det.op [shape, shape] shape
| binary_op.add     := det.cwise2.add shape
| binary_op.mul     := det.cwise2.mul shape
| binary_op.sub     := det.cwise2.sub shape
| binary_op.div     := det.cwise2.div shape

def get_id (next_id : ℕ) : option ID → ID
| none := ID.nat next_id
| (some ident) := ident

def process_term : term → state → option ID → reference × state

| (term.unary f t) st ident :=
    match process_term t st none with
    | ((p₁, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((ID.nat $ next_id, shape),
        ⟨next_id+1, shapes,
         concat nodes ⟨(get_id next_id ident, shape), [(p₁, shape)], operator.det (det.op.unary $ unary_to_cwise1 shape f)⟩,
         costs, targets, inputs⟩)
    end

| (term.binary f t₁ t₂) st ident :=
    match process_term t₁ st none with
    | ((p₁, shape'), st') :=
    match process_term t₂ st' none with
    | ((p₂, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((get_id next_id ident, shape),
       ⟨next_id+1, shapes,
        concat nodes ⟨(get_id next_id ident, shape), [(p₁, shape), (p₂, shape)], operator.det (det.op.binary $ binary_to_cwise2 shape f)⟩,
               costs, targets, inputs⟩)
    end
    end

| (term.sum t) st ident :=
    match process_term t st none with
    | ((p₁, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((get_id next_id ident, []),
        ⟨next_id+1, shapes,
         concat nodes ⟨(get_id next_id ident, []), [(p₁, shape)], operator.det (det.op.special (det.special.sum shape))⟩,
         costs, targets, inputs⟩)
    end

| (term.scale α t) st ident :=
    match process_term t st none with
    | ((p₁, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((get_id next_id ident, shape),
       ⟨next_id+1, shapes,
       concat nodes ⟨(get_id next_id ident, shape), [(p₁, shape)], operator.det (det.op.unary (det.cwise1.scale α))⟩,
       costs, targets, inputs⟩)
    end

| (term.gemm t₁ t₂) st ident :=
    match process_term t₁ st none with
    | ((p₁, shape₁), st') :=
    match process_term t₂ st' none with
    | ((p₂, shape₂), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      let m := shape₁.head, n := shape₂.head, p := shape₂.tail.head in
      ((get_id next_id ident, [m, p]),
       ⟨next_id+1, shapes,
        concat nodes ⟨(get_id next_id ident, [m, p]), [(p₁, [m, n]), (p₂, [n, p])], operator.det (det.op.special (det.special.gemm _ _ _))⟩,
        costs, targets, inputs⟩)
    end
    end

| (term.mvn_iso_kl t₁ t₂) st ident :=
    match process_term t₁ st none with
    | ((p₁, shape'), st') :=
    match process_term t₂ st' none with
    | ((p₂, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((get_id next_id ident, []), ⟨next_id+1, shapes,
        concat nodes ⟨(get_id next_id ident, []), [(p₁, shape), (p₂, shape)], operator.det (det.op.special $ det.special.mvn_iso_kl shape)⟩,
        costs, targets, inputs⟩)
    end
    end

| (term.mvn_iso_empirical_kl t₁ t₂ t₃) st ident :=
    match process_term t₁ st none with
    | ((p₁, shape''), st') :=
    match process_term t₂ st' none with
    | ((p₂, shape'), st'') :=
    match process_term t₃ st'' none with
    | ((p₃, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((get_id next_id ident, []), ⟨next_id+1, shapes,
        concat nodes ⟨(get_id next_id ident, []), [(p₁, shape), (p₂, shape), (p₃, shape)], operator.det (det.op.mvn_iso_empirical_kl shape)⟩,
        costs, targets, inputs⟩)
    end
    end
    end

| (term.bernoulli_neglogpdf t₁ t₂) st ident :=
    match process_term t₁ st none with
    | ((p₁, shape'), st') :=
    match process_term t₂ st' none with
    | ((p₂, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((get_id next_id ident, []),
        ⟨next_id+1, shapes,
         concat nodes ⟨(get_id next_id ident, []), [(p₁, shape), (p₂, shape)], operator.det (det.op.special $ det.special.bernoulli_neglogpdf shape)⟩,
         costs, targets, inputs⟩)
    end
    end

| (term.get_col_range t₁ t₂ ncols) st ident :=
    match process_term t₁ st none with
    | ((p₁, shape), st') :=
    match process_term t₂ st' none with
    | ((p₂, shape'), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      let m := shape.head, n := shape.tail.head in
      ((get_id next_id ident, [m, ncols]),
       ⟨next_id+1, shapes,
       concat nodes ⟨(get_id next_id ident, [m, ncols]), [(p₁, [m, n]), (p₂, [])], operator.det (det.op.special $ det.special.get_col_range m n ncols)⟩,
       costs, targets, inputs⟩)
    end
    end

| (term.id s) ⟨next_id, shapes, nodes, costs, targets, inputs⟩ ident :=
   match shapes^.find s with
   | (some shape) := ((ID.str s, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩)
   | none         := (default _, empty_state)
   end

def process_rterm : rterm → state → option ID → reference × state
| (rterm.mvn_iso t₁ t₂) st ident :=
    match process_term t₁ st none with
    | ((p₁, shape'), st') :=
    match process_term t₂ st' none with
    | ((p₂, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
      ((get_id next_id ident, shape),
        ⟨next_id+1, shapes,
         concat nodes ⟨(get_id next_id ident, shape), [(p₁, shape), (p₂, shape)], operator.rand (rand.op.mvn_iso shape)⟩,
         costs, targets, inputs⟩)
    end
    end

| (rterm.mvn_iso_std shape) ⟨next_id, shapes, nodes, costs, targets, inputs⟩ ident :=
  ((get_id next_id ident, shape),
   ⟨next_id+1, shapes,
    nodes ++ [⟨(get_id next_id ident, shape), [], operator.rand (rand.op.mvn_iso_std shape)⟩],
    costs, targets, inputs⟩)

def program_to_graph_core : list statement → state → state
| [] st := st

| (statement.assign s t::statements) st :=
  match process_term t st (some (ID.str s)) with
  | ((_, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
     program_to_graph_core statements ⟨next_id, shapes^.insert s shape, nodes, costs, targets, inputs⟩
  end

| (statement.sample s t::statements) st :=
  match process_rterm t st (some (ID.str s)) with
  | ((_, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) :=
    program_to_graph_core statements ⟨next_id, shapes^.insert s shape, nodes, costs, targets, inputs⟩
  end

| (statement.param s shape::statements) ⟨next_id, shapes, nodes, costs, targets, inputs⟩ :=
  program_to_graph_core statements ⟨next_id, shapes^.insert s shape, nodes, costs, concat targets (ID.str s, shape), concat inputs (ID.str s, shape)⟩
| (statement.input s shape::statements) ⟨next_id, shapes, nodes, costs, targets, inputs⟩ :=
  program_to_graph_core statements ⟨next_id, shapes^.insert s shape, nodes, costs, targets, concat inputs (ID.str s, shape)⟩
| (statement.cost s::statements) ⟨next_id, shapes, nodes, costs, targets, inputs⟩ :=
  program_to_graph_core statements ⟨next_id, shapes, nodes, concat costs (ID.str s), targets, inputs⟩

end program

def program := list program.statement

def program_to_graph : program → graph
| prog :=  match program.program_to_graph_core prog program.empty_state with
           | ⟨next_id, shapes, nodes, costs, targets, inputs⟩ := ⟨nodes, costs, targets, inputs⟩
           end

def mk_inputs : Π (g : graph), dvec T g^.inputs^.p2 → env
| g ws := env.insert_all g^.inputs ws

end certigrad
