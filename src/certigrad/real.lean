/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Real numbers.
-/
namespace certigrad

constant real : Type

namespace real

constants (zero one pi : real)
          (neg inv log exp sqrt tanh : real → real)
          (add mul sub div : real → real → real)
          (lt le : real → real → Prop)

constant pow : real → real → real
constant of_nat : ℕ → real
constant round : real → ℕ

end real
end certigrad
