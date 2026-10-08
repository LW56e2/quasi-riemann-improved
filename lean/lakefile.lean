import Lake
open Lake DSL

package RHTransport where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require «rellich-kondrachov» from git
  "https://github.com/abenenson/rellich-kondrachov.git" @ "70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23"

require PrimeNumberTheoremAnd from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @ "c39a751132c88b6e8080b74c74023fd95b3d8be0"

require LeanArchitect from git
  "https://github.com/hanwenzhu/LeanArchitect.git" @ "468e8f58fb4ad6e6ad672a08da6d0d0531e95a97"

require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git" @ "3d425859e73fcfbef85b9638c2a91708ef4a22d4"

require leancert from git
  "https://github.com/alerad/leancert.git" @ "7f91b6eb3567437f6cfac03ed279706603ee22f4"

require PrimeCert from git
  "https://github.com/b-mehta/PrimeCert.git" @ "0803c2f6bd289c09704c7d352bb8fcf770cbb9b2"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib OAI where
  globs := #[`OAI.+]

@[default_target] lean_lib Transport where
  globs := #[`Transport.+]
