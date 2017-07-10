/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

References.
-/
import .id .tensor .util

namespace certigrad

@[reducible] def reference := ID × S

namespace reference

-- TODO(dhs): (much) better hash function
def hash : reference → ℕ
| ref := 0

end reference
end certigrad
