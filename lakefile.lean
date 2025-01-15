import Lake
open Lake DSL

package «lean-machines-examples» where
  -- add package configuration options here

lean_lib «LeanMachinesExamples» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-machines-examples» where
  root := `Main

require «lean-machines» from git
  "https://github.com/lean-machines-central/lean-machines.git" @ "PO_guards"

