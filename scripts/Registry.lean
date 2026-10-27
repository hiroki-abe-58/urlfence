import UrlFence

/-! The registry tables of `UrlFence.Addr` for `scripts/check_registry.py`, one row per line:
`ROW4|<block as printed>|<base as a number>|<length>|<Globally Reachable>|<name>`, and `ROW6` likewise. -/

open UrlFence.Addr

def reachText : Reach → String
  | .yes => "True"
  | .no => "False"
  | .na => "N/A"
  | .blank => ""

#eval show IO Unit from do
  for r in ipv4Registry do
    IO.println s!"ROW4|{(UrlFence.Addr.v4 r.block.base).toString}/{r.block.len}|{r.block.base.toNat}|{r.block.len}|{reachText r.reachable}|{r.name}"
  for r in ipv6Registry do
    IO.println s!"ROW6|{(UrlFence.Addr.v6 r.block.base).toString}/{r.block.len}|{r.block.base.toNat}|{r.block.len}|{reachText r.reachable}|{r.name}"
