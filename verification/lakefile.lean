import Lake
open Lake DSL

package rowlVerification where
  moreLeanArgs := #["-DwarningAsError=true"]

require aeneas from "../.tools/aeneas/backends/lean"

@[default_target]
lean_lib Rowl where
  roots := #[`Rowl]
