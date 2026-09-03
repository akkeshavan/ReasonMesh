import Lake
open Lake DSL

/-!
# RmApi — Lean 4 package for ReasonMesh

## Quick start

  1. Build the Rust shared library first:
       cd .. && cargo build --release -p rm-api

  2. Build this package:
       cd lean && lake build

  3. Run tests:
       lake test

The library is searched for at `../target/release/librm_api.{dylib,so}`.
Set `RM_API_LIB_DIR` to override.
-/

package «RmApi» where
  name := "RmApi"
  -- Link against the Rust shared library.
  -- `lake build` will find it via LIBRARY_PATH / LD_LIBRARY_PATH, or
  -- set RM_API_LIB_DIR before invoking lake.
  moreLinkArgs := #[
    s!"-L{__dir__}/../target/release",
    "-lrm_api",
    -- Embed the rpath so the binary finds librm_api at runtime without
    -- requiring LD_LIBRARY_PATH to be set by the end user.
    s!"-Wl,-rpath,{__dir__}/../target/release"
  ]

lean_lib «RmApi» where
  roots := #[`RmApi]

lean_exe «RmApiTest» where
  root := `test.RmApiTest

/-!
Compile `ffi/rm_lean_ffi.c` as an extern library object.
It is linked into every Lean target that depends on RmApi.
-/
extern_lib «libRmLeanFfi» (pkg : Package) : LakeM (BuildJob FilePath) := do
  let leanInc ← getLeanIncludeDir
  let apiInc  := pkg.dir / ".." / "crates" / "rm-api" / "include"
  let srcFile := pkg.dir / "ffi" / "rm_lean_ffi.c"
  let oFile   := pkg.buildDir / "ffi" / "rm_lean_ffi.o"
  let srcJob  ← inputTextFile srcFile
  compileO "rm_lean_ffi.c" oFile srcJob
    #["-fPIC",
      "-I", leanInc.toString,
      "-I", apiInc.toString]
    "cc"
