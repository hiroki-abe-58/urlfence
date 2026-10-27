import UrlFence.Addr.Bits

/-!
# The IANA special-purpose address registries

The IPv4 and IPv6 Special-Purpose Address Registries as last updated by IANA on 2025-10-09,
transcribed from the CSV files kept in `data/` (see `data/README.md`): for each row, the address
block, the name and the "Globally Reachable" column. The row `192.0.0.170/32, 192.0.0.171/32` of the
IPv4 registry is one row per block here. Footnote marks are dropped from the column values; the
footnotes are quoted in `data/README.md`. `scripts/check_registry.py` compares these tables with the
CSV files.

Every block is a well-formed CIDR block: its length is at most the address width and its bits after
the prefix are zero (`ipv4Registry_blocks`, `ipv6Registry_blocks`), so membership is a range of
addresses (`contains_iff_range4`, `contains_iff_range6`).
-/

namespace UrlFence.Addr

/-- The "Globally Reachable" column. -/
inductive Reach where
  /-- `True` -/
  | yes
  /-- `False` -/
  | no
  /-- `N/A` -/
  | na
  /-- Empty: the rows of terminated allocations. -/
  | blank
  deriving DecidableEq, Repr

/-- One row of a registry. -/
structure Row (w : Nat) where
  block : Prefix w
  name : String
  reachable : Reach
  deriving Repr

/-- The IPv4 address `a.b.c.d`. -/
def ip4 (a b c d : Nat) : BitVec 32 := BitVec.ofNat 32 (ofDigits 256 [a, b, c, d])

/-- The IPv6 address with these eight 16-bit groups. -/
def ip6 (gs : List Nat) : BitVec 128 := BitVec.ofNat 128 (ofDigits 65536 gs)

/-- The IANA IPv4 Special-Purpose Address Registry, in its order. -/
def ipv4Registry : List (Row 32) := [
  ⟨⟨ip4 0 0 0 0, 8⟩, "\"This network\"", .no⟩,
  ⟨⟨ip4 0 0 0 0, 32⟩, "\"This host on this network\"", .no⟩,
  ⟨⟨ip4 10 0 0 0, 8⟩, "Private-Use", .no⟩,
  ⟨⟨ip4 100 64 0 0, 10⟩, "Shared Address Space", .no⟩,
  ⟨⟨ip4 127 0 0 0, 8⟩, "Loopback", .no⟩,
  ⟨⟨ip4 169 254 0 0, 16⟩, "Link Local", .no⟩,
  ⟨⟨ip4 172 16 0 0, 12⟩, "Private-Use", .no⟩,
  ⟨⟨ip4 192 0 0 0, 24⟩, "IETF Protocol Assignments", .no⟩,
  ⟨⟨ip4 192 0 0 0, 29⟩, "IPv4 Service Continuity Prefix", .no⟩,
  ⟨⟨ip4 192 0 0 8, 32⟩, "IPv4 dummy address", .no⟩,
  ⟨⟨ip4 192 0 0 9, 32⟩, "Port Control Protocol Anycast", .yes⟩,
  ⟨⟨ip4 192 0 0 10, 32⟩, "Traversal Using Relays around NAT Anycast", .yes⟩,
  ⟨⟨ip4 192 0 0 170, 32⟩, "NAT64/DNS64 Discovery", .no⟩,
  ⟨⟨ip4 192 0 0 171, 32⟩, "NAT64/DNS64 Discovery", .no⟩,
  ⟨⟨ip4 192 0 2 0, 24⟩, "Documentation (TEST-NET-1)", .no⟩,
  ⟨⟨ip4 192 31 196 0, 24⟩, "AS112-v4", .yes⟩,
  ⟨⟨ip4 192 52 193 0, 24⟩, "AMT", .yes⟩,
  ⟨⟨ip4 192 88 99 0, 24⟩, "Deprecated (6to4 Relay Anycast)", .blank⟩,
  ⟨⟨ip4 192 88 99 2, 32⟩, "6a44-relay anycast address", .no⟩,
  ⟨⟨ip4 192 168 0 0, 16⟩, "Private-Use", .no⟩,
  ⟨⟨ip4 192 175 48 0, 24⟩, "Direct Delegation AS112 Service", .yes⟩,
  ⟨⟨ip4 198 18 0 0, 15⟩, "Benchmarking", .no⟩,
  ⟨⟨ip4 198 51 100 0, 24⟩, "Documentation (TEST-NET-2)", .no⟩,
  ⟨⟨ip4 203 0 113 0, 24⟩, "Documentation (TEST-NET-3)", .no⟩,
  ⟨⟨ip4 240 0 0 0, 4⟩, "Reserved", .no⟩,
  ⟨⟨ip4 255 255 255 255, 32⟩, "Limited Broadcast", .no⟩]

/-- The IANA IPv6 Special-Purpose Address Registry, in its order. -/
def ipv6Registry : List (Row 128) := [
  ⟨⟨ip6 [0, 0, 0, 0, 0, 0, 0, 1], 128⟩, "Loopback Address", .no⟩,
  ⟨⟨ip6 [0, 0, 0, 0, 0, 0, 0, 0], 128⟩, "Unspecified Address", .no⟩,
  ⟨⟨ip6 [0, 0, 0, 0, 0, 0xffff, 0, 0], 96⟩, "IPv4-mapped Address", .no⟩,
  ⟨⟨ip6 [0x64, 0xff9b, 0, 0, 0, 0, 0, 0], 96⟩, "IPv4-IPv6 Translat.", .yes⟩,
  ⟨⟨ip6 [0x64, 0xff9b, 1, 0, 0, 0, 0, 0], 48⟩, "IPv4-IPv6 Translat.", .no⟩,
  ⟨⟨ip6 [0x100, 0, 0, 0, 0, 0, 0, 0], 64⟩, "Discard-Only Address Block", .no⟩,
  ⟨⟨ip6 [0x100, 0, 0, 1, 0, 0, 0, 0], 64⟩, "Dummy IPv6 Prefix", .no⟩,
  ⟨⟨ip6 [0x2001, 0, 0, 0, 0, 0, 0, 0], 23⟩, "IETF Protocol Assignments", .no⟩,
  ⟨⟨ip6 [0x2001, 0, 0, 0, 0, 0, 0, 0], 32⟩, "TEREDO", .na⟩,
  ⟨⟨ip6 [0x2001, 1, 0, 0, 0, 0, 0, 1], 128⟩, "Port Control Protocol Anycast", .yes⟩,
  ⟨⟨ip6 [0x2001, 1, 0, 0, 0, 0, 0, 2], 128⟩, "Traversal Using Relays around NAT Anycast", .yes⟩,
  ⟨⟨ip6 [0x2001, 1, 0, 0, 0, 0, 0, 3], 128⟩, "DNS-SD Service Registration Protocol Anycast", .yes⟩,
  ⟨⟨ip6 [0x2001, 2, 0, 0, 0, 0, 0, 0], 48⟩, "Benchmarking", .no⟩,
  ⟨⟨ip6 [0x2001, 3, 0, 0, 0, 0, 0, 0], 32⟩, "AMT", .yes⟩,
  ⟨⟨ip6 [0x2001, 4, 0x112, 0, 0, 0, 0, 0], 48⟩, "AS112-v6", .yes⟩,
  ⟨⟨ip6 [0x2001, 0x10, 0, 0, 0, 0, 0, 0], 28⟩, "Deprecated (previously ORCHID)", .blank⟩,
  ⟨⟨ip6 [0x2001, 0x20, 0, 0, 0, 0, 0, 0], 28⟩, "ORCHIDv2", .yes⟩,
  ⟨⟨ip6 [0x2001, 0x30, 0, 0, 0, 0, 0, 0], 28⟩, "Drone Remote ID Protocol Entity Tags (DETs) Prefix", .yes⟩,
  ⟨⟨ip6 [0x2001, 0xdb8, 0, 0, 0, 0, 0, 0], 32⟩, "Documentation", .no⟩,
  ⟨⟨ip6 [0x2002, 0, 0, 0, 0, 0, 0, 0], 16⟩, "6to4", .na⟩,
  ⟨⟨ip6 [0x2620, 0x4f, 0x8000, 0, 0, 0, 0, 0], 48⟩, "Direct Delegation AS112 Service", .yes⟩,
  ⟨⟨ip6 [0x3fff, 0, 0, 0, 0, 0, 0, 0], 20⟩, "Documentation", .no⟩,
  ⟨⟨ip6 [0x5f00, 0, 0, 0, 0, 0, 0, 0], 16⟩, "Segment Routing (SRv6) SIDs", .no⟩,
  ⟨⟨ip6 [0xfc00, 0, 0, 0, 0, 0, 0, 0], 7⟩, "Unique-Local", .no⟩,
  ⟨⟨ip6 [0xfe80, 0, 0, 0, 0, 0, 0, 0], 10⟩, "Link-Local Unicast", .no⟩]

/-- Every IPv4 block is a CIDR block: at most 32 bits long, zero after them. -/
theorem ipv4Registry_blocks :
    ∀ r ∈ ipv4Registry, r.block.len ≤ 32 ∧ r.block.base.toNat % 2 ^ (32 - r.block.len) = 0 := by
  decide +kernel

/-- Every IPv6 block is a CIDR block: at most 128 bits long, zero after them. -/
theorem ipv6Registry_blocks :
    ∀ r ∈ ipv6Registry, r.block.len ≤ 128 ∧ r.block.base.toNat % 2 ^ (128 - r.block.len) = 0 := by
  decide +kernel

/-- An address is in the block of an IPv4 row exactly when it is in the block's range. -/
theorem contains_iff_range4 (r : Row 32) (hr : r ∈ ipv4Registry) (a : BitVec 32) :
    r.block.contains a = true ↔
      r.block.base.toNat ≤ a.toNat ∧ a.toNat < r.block.base.toNat + 2 ^ (32 - r.block.len) :=
  Prefix.contains_iff_range _ _ (ipv4Registry_blocks r hr).2

/-- An address is in the block of an IPv6 row exactly when it is in the block's range. -/
theorem contains_iff_range6 (r : Row 128) (hr : r ∈ ipv6Registry) (a : BitVec 128) :
    r.block.contains a = true ↔
      r.block.base.toNat ≤ a.toNat ∧ a.toNat < r.block.base.toNat + 2 ^ (128 - r.block.len) :=
  Prefix.contains_iff_range _ _ (ipv6Registry_blocks r hr).2

end UrlFence.Addr
