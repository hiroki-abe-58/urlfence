import UrlFence
import Lean

/-! Facts about the UrlFence modules for `scripts/audit.sh`, one line each:

* `AXIOMS <kind> <name>: [<axioms>]` for every declaration (private ones included), with the axioms
  it depends on. The list is generated, so it does not have to be kept by hand.
* `IMPORT <module> <imported>` for every import of a UrlFence module. Only `Init` and UrlFence
  modules may be imported, so no other code can reach the library.
* `IMPLBY <name> <impl>` and `EXTERN <name>` for every UrlFence declaration whose compiled code is
  replaced (`implemented_by`, `extern`). There must be none: the binary must run the code the
  theorems are about.
* `STATEMENT <name> : <type>` for every theorem, pretty-printed on one line, so that the published
  statements can be compared with `scripts/statements.expected`.
* `DEPS <name> <dep> …` for every theorem: every UrlFence constant its statement depends on,
  directly or indirectly (through types and definition bodies, not proofs; an inductive type brings
  its constructors and recursor), and `CANON <name> <text>` for every UrlFence constant: its type,
  value and constructors as raw terms (implicit arguments and instances included). `audit.sh`
  hashes a statement's `CANON` lines with SHA-256, so a change to `domainOk`, `parse`, a
  constructor list or anything else a statement refers to changes the pin, even when the printed
  statement stays the same. -/

open Lean Elab Command

/-- The UrlFence constants reachable from `todo` through types and definition bodies (theorem
proofs are not followed). -/
partial def depClosure (env : Environment) (isOurs : Name → Bool) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then depClosure env isOurs rest seen else
    let ours := (env.getModuleIdxFor? n).bind (fun i => env.header.moduleNames[i.toNat]?) |>.map isOurs
    if ours != some true then depClosure env isOurs rest seen else
    match env.find? n with
    | none => depClosure env isOurs rest seen
    | some ci =>
      let body := match ci with
        | .thmInfo _ => []
        | _ => (ci.value?.map Expr.getUsedConstants).getD #[] |>.toList
      let family := match ci with
        | .inductInfo v => v.ctors ++ [mkRecName n]
        | .ctorInfo v => [v.induct]
        | _ => []
      depClosure env isOurs (ci.type.getUsedConstants.toList ++ body ++ family ++ rest) (seen.insert n)

/-- The UrlFence constants a theorem's statement depends on, sorted. -/
def statementDeps (env : Environment) (isOurs : Name → Bool) (ci : ConstantInfo) : Array Name :=
  (depClosure env isOurs ci.type.getUsedConstants.toList {}).toList.toArray.qsort
    (fun a b => a.toString < b.toString)

/-- A constant as one line of raw terms: type, value (not for theorems) and, for an inductive type,
its constructors, parameters and indices. -/
def canon (ci : ConstantInfo) : String :=
  let value := match ci with
    | .thmInfo _ => ""
    | _ => (ci.value?.map toString).getD ""
  let family := match ci with
    | .inductInfo v => s!" ctors={v.ctors} params={v.numParams} indices={v.numIndices}"
    | .ctorInfo v => s!" induct={v.induct} cidx={v.cidx} fields={v.numFields}"
    | _ => ""
  -- Escape, not replace: a string literal "a\nb" must not print like "a b".
  (s!"{ci.type} := {value}{family}").replace "\\" "\\\\" |>.replace "\n" "\\n"

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
    -- Names are split on spaces below; refuse any that contain whitespace.
    if name.toString.any Char.isWhitespace then
      lines := lines.push s!"BADNAME {name}"
    lines := lines.push s!"CANON {name} {canon ci}"
    let axs ← collectAxioms name
    lines := lines.push s!"AXIOMS {kind} {name}: {axs.toList}"
    if kind == "theorem" then
      let fmt ← liftTermElabM (Meta.ppExpr ci.type)
      let raw := (fmt.pretty 100000).replace "\n" " "
      let stmt := " ".intercalate ((raw.splitOn " ").filter (· ≠ ""))
      lines := lines.push s!"STATEMENT {name} : {stmt}"
      lines := lines.push s!"DEPS {name} {" ".intercalate ((statementDeps env isOurs ci).toList.map toString)}"
    if let some impl := Compiler.getImplementedBy? env name then
      lines := lines.push s!"IMPLBY {name} {impl}"
    if isExtern env name then
      lines := lines.push s!"EXTERN {name}"
  for l in lines.qsort (· < ·) do
    IO.println l
