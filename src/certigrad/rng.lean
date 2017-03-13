/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Random number generators.
-/
namespace certigrad
open list

constant RNG : Type

namespace RNG
constant mk : ℕ → RNG
constant to_string : RNG → string

instance : has_to_string RNG := has_to_string.mk to_string
end RNG
end certigrad
