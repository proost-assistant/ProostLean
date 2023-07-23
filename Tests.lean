def IotaArr (size : Nat) := Id.run do
  let mut arr := Array.mkEmpty size
  for i in [0:size] do
    arr := arr.push i
  arr

def main : IO Unit :=
  let arr := IotaArr 100000000
  IO.println s!"Hello, {arr[10000]!}!"

#eval main


/-syntax "open_all" ident : command

#check elabCommand

def foo (i : TSyntax `ident) : TSyntax `Lean.Parser.Command.openDecl := 
  i.getName

elab "open_all" i:ident : command => do
  let env ← getEnv
  let name := i.getId
  if isStructure env name then
    let parents := getParentStructures env name
    for parent in parents do
      let stx ← `(open $parent)
      elabCommand stx
  let stx ← `(open $i)
  elabCommand stx-/