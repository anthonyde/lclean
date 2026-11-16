import Lake
open Lake DSL

package lclean

@[default_target]
lean_lib LC where
  roots := #[`LC]

def leanVersion : String := s!"v{Lean.versionString}"

require "leanprover-community" / mathlib @ s!"git#{leanVersion}"
