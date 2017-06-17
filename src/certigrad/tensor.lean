/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Tensors and basic tensor operations.
-/
import library_dev_extras.util .rng .dvec .id .real

run_cmd mk_simp_attr `cgsimp

namespace certigrad

@[reducible] def S : Type := list ℕ

constant T (shape : S) : Type
notation `ℝ` := T []

namespace T

-- Constants that compute (excluding const, lt, le)

constant const (α : ℝ) (shape : S) : T shape

constant zero (shape : S) : T shape
constant one (shape : S) : T shape
constant pi (shape : S) : T shape

constant neg {shape : S} (x : T shape) : T shape
constant inv {shape : S} (x : T shape) : T shape
constant log {shape : S} (x : T shape) : T shape
constant exp {shape : S} (x : T shape) : T shape
constant sqrt {shape : S} (x : T shape) : T shape
constant tanh {shape : S} (x : T shape) : T shape

constant add {shape : S} (x y : T shape) : T shape
constant mul {shape : S} (x y : T shape) : T shape
constant sub {shape : S} (x y : T shape) : T shape
constant div {shape : S} (x y : T shape) : T shape

constant lt {shape : S} (x y : T shape) : Prop
constant le {shape : S} (x y : T shape) : Prop

constant pow {shape : S} (x : T shape) (α : ℝ) : T shape
constant of_nat (n : ℕ) : ℝ
constant round (α : ℝ) : ℕ

constant fail (shape : S) : T shape
constant silent_fail (shape : S) : T shape
constant error {shape : S} (s : string) : T shape

-- Algebraic instances
@[inline, priority 10000] instance (shape : S) : has_zero (T shape) := ⟨T.zero shape⟩
@[inline, priority 10000] instance (shape : S) : has_one (T shape) := ⟨T.one shape⟩
@[inline, priority 10000] instance (shape : S) : has_neg (T shape) := ⟨T.neg⟩
@[inline, priority 10000] instance (shape : S) : has_add (T shape) := ⟨T.add⟩
@[inline, priority 10000] instance (shape : S) : has_mul (T shape) := ⟨T.mul⟩
@[inline, priority 10000] instance (shape : S) : has_lt (T shape) := ⟨T.lt⟩
@[inline, priority 10000] instance (shape : S) : has_le (T shape) := ⟨T.le⟩
@[inline, priority 10000] instance (shape : S) : has_inv (T shape) := ⟨T.inv⟩
@[inline, priority 10000] instance (shape : S) : has_div (T shape) := ⟨λ x y, x * y⁻¹⟩

namespace IL
-- Instance Lemmas
axiom add_comm {shape : S} : ∀ (x y : T shape), x + y = y + x
axiom add_assoc {shape : S} : ∀ (x y z : T shape), x + y + z = x + (y + z)
axiom zero_add {shape : S} : ∀ (x : T shape), 0 + x = x
axiom add_zero {shape : S} : ∀ (x : T shape), x + 0 = x
axiom add_left_neg {shape : S} : ∀ (x : T shape), -x + x = 0
axiom mul_comm {shape : S} : ∀ (x y : T shape), x * y = y * x
axiom mul_assoc  {shape : S} : ∀ (x y z : T shape), x * y * z = x * (y * z)
axiom one_mul {shape : S} : ∀ (x : T shape), 1 * x = x
axiom mul_one {shape : S} : ∀ (x : T shape), x * 1 = x
axiom left_distrib {shape : S} : ∀ (x y z : T shape), x * (y + z) = x * y + x * z
axiom right_distrib {shape : S} : ∀ (x y z : T shape), (x + y) * z = x * z + y * z
axiom le_refl {shape : S} : ∀ (x : T shape), x ≤ x
axiom le_trans {shape : S} : ∀ (x y z : T shape), x ≤ y → y ≤ z → x ≤ z
axiom le_antisymm {shape : S} : ∀ (x y : T shape), x ≤ y → y ≤ x → x = y
axiom le_of_lt {shape : S} : ∀ (x y : T shape), x < y → x ≤ y
axiom lt_of_lt_of_le {shape : S} : ∀ (x y z : T shape), x < y → y ≤ z → x < z
axiom lt_of_le_of_lt {shape : S} : ∀ (x y z : T shape), x ≤ y → y < z → x < z
axiom lt_irrefl {shape : S} : ∀ (x : T shape), ¬x < x
axiom add_le_add_left {shape : S} : ∀ (x y : T shape), x ≤ y → ∀ (z : T shape), z + x ≤ z + y
axiom add_lt_add_left {shape : S} : ∀ (x y : T shape), x < y → ∀ (z : T shape), z + x < z + y
axiom zero_ne_one {shape : S} : (0 : T shape) ≠ (1 : T shape)
axiom mul_nonneg {shape : S} : ∀ (x y : T shape), 0 ≤ x → 0 ≤ y → 0 ≤ x * y
axiom mul_pos {shape : S} : ∀ (x y : T shape), 0 < x → 0 < y → 0 < x * y
axiom le_iff_lt_or_eq {shape : S} : ∀ (x y : T shape), x ≤ y ↔ x < y ∨ x = y
end IL
@[inline] instance (shape : S) : ordered_comm_ring (T shape) :=
{
  -- defs
  zero := T.zero shape, one := T.one shape, add := T.add, neg := T.neg, mul := T.mul,
  -- noncomputable defs
  le := T.le, lt := T.lt,
  -- axioms
  add_comm := T.IL.add_comm, add_assoc := T.IL.add_assoc, zero_add := T.IL.zero_add,
  add_zero := T.IL.add_zero, add_left_neg := T.IL.add_left_neg,
  mul_comm := T.IL.mul_comm, mul_assoc := T.IL.mul_assoc, one_mul := T.IL.one_mul, mul_one := T.IL.mul_one,
  left_distrib := T.IL.left_distrib, right_distrib := T.IL.right_distrib,
  le_refl := T.IL.le_refl, le_trans := T.IL.le_trans, le_antisymm := T.IL.le_antisymm,
  le_of_lt := T.IL.le_of_lt, lt_of_lt_of_le := T.IL.lt_of_lt_of_le, lt_of_le_of_lt := T.IL.lt_of_le_of_lt,
  lt_irrefl := T.IL.lt_irrefl, add_le_add_left := T.IL.add_le_add_left, add_lt_add_left := T.IL.add_lt_add_left,
  zero_ne_one := T.IL.zero_ne_one, mul_nonneg := T.IL.mul_nonneg, mul_pos := T.IL.mul_pos
}

@[inline] instance (shape : S) : has_sub (T shape) := by apply_instance
attribute [inline] ordered_comm_ring.to_ordered_ring ordered_ring.to_ring ring.to_add_comm_group add_comm_group.to_add_group algebra.sub

-- We never want to do algebra with this
def scalar_mul {shape : S} (α : ℝ) (x : T shape) : T shape := const α shape * x

constant transpose {m n : ℕ} (M : T [m, n]) : T [n, m]

constant sum : Π {shape : S}, T shape → ℝ
constant prod : Π {shape : S}, T shape → ℝ

constant get_row {m n : ℕ} (M : T [m, n]) (ridx : ℕ) : T [n]
constant sum_cols {nrows ncols : ℕ} (M : T [nrows, ncols]) : T [nrows]
constant get_col {m n : ℕ} (M : T [m, n]) (cidx : ℕ) : T [m]

constant get_col_range {m n : ℕ} (ncols : ℕ) (M : T [m, n]) (cidx : ℕ) : T [m, ncols]
constant replicate_col {m : ℕ} (v : T [m]) (n : ℕ) : T [m, n]

constant gemv {m n : ℕ} (M : T [m, n]) (x : T [n]) : T [m]
constant gemm {m n p : ℕ} (M : T [m, n]) (N : T [n, p]) : T [m, p]

constant append_col {n p : ℕ} (N : T [n, p]) (x : T [n]) : T [n, p+1]

constant sample_mvn_iso : Π {shape : S} (μ σ : T shape) (rng : RNG), T shape × RNG
constant sample_uniform : Π (shape : S) (low high : ℝ) (rng : RNG), T shape × RNG

constant to_string {shape : S} : T shape → string

/- Other constants -/

constant is_integrable : Π {shape₁ shape₂ : S}, (T shape₁ → T shape₂) → Prop
constant integral : Π {shape₁ shape₂ : S}, (T shape₁ → T shape₂) → T shape₂

constant is_uniformly_integrable_around : Π {shape₁ shape₂ shape₃ : S} (f : T shape₁ → T shape₂ → T shape₃) (θ : T shape₁), Prop

-- ω(exp -x²) ∧ o(exp x²)
constant is_btw_exp₂ {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : Prop
constant is_sub_quadratic {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : Prop
constant is_bounded_btw_exp₂_around {shape₁ shape₂ shape₃ : S} (f : Π (x : T shape₁) (θ : T shape₂), T shape₃) (θ : T shape₂) : Prop

-- continuously differentiable
constant is_cdifferentiable : Π {ishape : S}, (T ishape → ℝ) → T ishape → Prop
constant grad : Π {ishape : S}, (T ishape → ℝ) → (T ishape → T ishape)
constant D {ishape oshape : S} : (T ishape → T oshape) → T ishape → T (ishape ++ oshape)
constant tmulT {ishape oshape : S} : T (ishape ++ oshape) → T oshape → T ishape
constant is_continuous {ishape oshape : S} : (T ishape → T oshape) → T ishape → Prop

noncomputable def dintegral {oshape : S} : Π {ishapes : list S}, (dvec T ishapes → T oshape) → T oshape
| []                f := f ⟦⟧
| (ishape::ishapes) f := integral (λ (x : T ishape), @dintegral ishapes (λ (v : dvec T ishapes), f (x ::: v)))

noncomputable def is_dintegrable {oshape : S} : Π {ishapes : list S}, (dvec T ishapes → T oshape) → Prop
| [] f := true
| (ishape::ishapes) f := is_integrable (λ (x : T ishape), @dintegral _ ishapes (λ (v : dvec T ishapes), f (x ::: v)))
                         ∧ ∀ (x : T ishape), is_dintegrable (λ (v : dvec T ishapes), f (x ::: v))

/- Notation -/

notation `π` := pi []
notation `∫` := integral
notation `∇` := grad

/- Other instances -/

instance {shape : S} : has_to_string (T shape) := has_to_string.mk T.to_string
@[inline] instance {shape : S} : inhabited (T shape) := ⟨silent_fail _⟩ --⟨T.zero shape⟩ (switch back once no course-of-values)
@[inline] instance {shape : S} : has_smul (ℝ) (T shape) := ⟨scalar_mul⟩

/- Derived definitions -/

def softplus {shape : S} (x : T shape) : T shape := log (exp x + 1)
def sigmoid {shape : S} (x : T shape) : T shape := 1 / (1 + exp (- x))
def dot {shape : S} (x y : T shape) : ℝ := sum (x * y)

def square {shape : S} (x : T shape) : T shape := x * x

def mvn_iso_pdf {shape : S} (μ σ x : T shape) : ℝ :=
  prod ((sqrt ((2 * pi shape) * square σ))⁻¹ * exp ((- 2⁻¹) * (square $ (x - μ) / σ)))

def mvn_iso_logpdf {shape : S} (μ σ x : T shape) : ℝ :=
  (- 2⁻¹) * sum (square ((x - μ) / σ) + log (2 * pi shape) + log (square σ))

def mvn_iso_grad_logpdf_μ {shape : S} (μ σ x : T shape) : T shape :=
  (x - μ) / (square σ)

def mvn_iso_grad_logpdf_σ {shape : S} (μ σ x : T shape) : T shape :=
  square (x - μ) / (σ * square σ) - σ⁻¹

def mvn_iso_std_logpdf {shape : S} (x : T shape) : ℝ := mvn_iso_logpdf 0 1 x

def mvn_iso_kl {shape : S} (μ σ : T shape) : ℝ :=
  (- 2⁻¹) * sum (1 + log (square σ) - square μ - square σ)

def mvn_iso_empirical_kl {shape : S} (μ σ z : T shape) : ℝ :=
  mvn_iso_logpdf μ σ z - mvn_iso_std_logpdf z

def bernoulli_neglogpdf {shape : S} (p z : T shape) : ℝ :=
  - sum (z * log p + (1 - z) * log (1 - p))

def force {shape₁ : S} (x : T shape₁) (shape₂ : S) : T shape₂ :=
  if H : shape₁ = shape₂ then eq.rec_on H x else T.error ("force-failed: " ++ _root_.to_string shape₁ ++ " != " ++ _root_.to_string shape₂)

end T
end certigrad
