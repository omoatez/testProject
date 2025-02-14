import Lake
open Lake DSL

package «testProject» where
  -- add package configuration options here
@[default_target]
lean_lib «TestProject» where

  -- add library configuration options here
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "v4.12.0"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"
