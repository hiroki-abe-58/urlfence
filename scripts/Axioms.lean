import UrlFence
import Lean

/-! Facts about the UrlFence modules for `scripts/audit.sh`, one line each:

* `AXIOMS <kind> <name>: [<axioms>]` for every declaration (private ones included), with the axioms
  it depends on. The list is generated, so it does not have to be kept by hand.
* `IMPORT <module> <imported>` for every import of a UrlFence module. Only `Init` and UrlFence
  modules may be imported, so no other code can reach the library.
* `IMPLBY <name> <impl>` and `EXTERN <name>` for every UrlFence declaration whose compiled code is
  replaced (`implemented_by`, `extern`). There must be none: the binary must run the code the
  theorems are about. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut lines : Array String := #[]
  let isOurs (m : Name) : Bool := (`UrlFence).isPrefixOf m
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    unless isOurs m do continue
    for imp in (env.header.moduleData[i]?.map (·.imports)).getD #[] do
      lines := lines.push s!"IMPORT {m} {imp.module}"
  for (name, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless isOurs m do continue
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque"
      | _ => "def"
    let axs ← collectAxioms name
    lines := lines.push s!"AXIOMS {kind} {name}: {axs.toList}"
    if let some impl := Compiler.getImplementedBy? env name then
      lines := lines.push s!"IMPLBY {name} {impl}"
    if isExtern env name then
      lines := lines.push s!"EXTERN {name}"
  for l in lines.qsort (· < ·) do
    IO.println l
