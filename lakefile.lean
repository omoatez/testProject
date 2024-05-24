import Lake
open Lake DSL

package «testProject» where
  -- add package configuration options here

lean_lib «TestProject» where

  -- add library configuration options here
require std from git
  "https://github.com/leanprover/std4" @ "main"
