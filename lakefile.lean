import Lake
open Lake DSL

package urlfence where
  version := v!"0.1.0"
  description := "Verified URL host allowlist checks for AI-agent web tools"
  keywords := #["security", "url", "ssrf", "verification"]
  license := "Apache-2.0"

@[default_target]
lean_lib UrlFence

@[default_target]
lean_exe urlfence where
  root := `Main
