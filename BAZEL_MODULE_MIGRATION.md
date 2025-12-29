# Bazel Module Migration Summary

This document summarizes the migration of dReal4 from legacy WORKSPACE to the modern Bazel module system (bzlmod).

## Changes Made

### 1. Created MODULE.bazel
- Replaced WORKSPACE configuration with MODULE.bazel
- Added core dependencies from Bazel Central Registry:
  - bazel_skylib@1.9.0
  - platforms@1.0.0  
  - rules_python@1.7.0
  - rules_license@1.0.0
  - rules_pkg@1.2.0
  - googletest@1.17.0
  - abseil-cpp@20250814.1

### 2. External Dependencies
- Migrated third-party dependencies to use git_repository and http_archive
- Fixed git repository references to use proper `tag` instead of `commit` for version tags
- Dependencies include: spdlog, fmt, picosat, pybind11, cds, json, ezoptionparser

### 3. System Dependencies
- Maintained pkg_config_repository for system libraries (ibex, nlopt, gmp)
- Created custom BUILD templates (tools/ibex.BUILD.tpl, tools/nlopt.BUILD.tpl) to fix target naming issues in bzlmod
- Preserved local_config_python for Python toolchain compatibility

### 4. Updated .bazelrc
- Enabled bzlmod: `--enable_bzlmod`
- Removed legacy WORKSPACE flags: `--noenable_bzlmod --enable_workspace`

## Key Fixes

### Target Naming Issue
The pkg_config_repository rule generates mangled repository names in bzlmod, causing target reference failures. Fixed by:
1. Creating custom BUILD templates with hardcoded target names
2. Using `build_file_template` parameter in pkg_config_repository calls

### Git Repository References
- Changed `commit = "v1.16.0"` to `tag = "v1.16.0"` for version tags
- Kept commit hashes for non-tagged dependencies

### Python Toolchain
- Used existing local_config_python approach instead of rules_python extensions
- Registered toolchain with `register_toolchains("@local_config_python//:py_toolchain")`

## Verification

✅ Basic build: `bazel build --nobuild`
✅ Utility build: `bazel build //dreal/util:logging`  
✅ Main executable: `bazel build //dreal:dreal`
✅ Unit tests: `bazel test //dreal/util:logging_test`

## Benefits

1. **Future-proof**: Uses modern Bazel module system (bzlmod)
2. **Reproducible**: Locked dependency versions from Bazel Central Registry
3. **Maintainable**: Cleaner dependency management
4. **Compatible**: Maintains all existing functionality

## Files Modified

- `MODULE.bazel` (new)
- `.bazelrc` (updated)
- `tools/ibex.BUILD.tpl` (new)
- `tools/nlopt.BUILD.tpl` (new)

The migration is complete and the project now uses the modern Bazel module system while maintaining full compatibility with existing build targets and tests.
