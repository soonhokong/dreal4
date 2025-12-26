"""Override local_config_python to use Python 3 only."""

def _local_config_python_impl(repository_ctx):
    python3 = repository_ctx.which("python3")
    if not python3:
        fail("python3 not found")
    
    # Get Python include path
    result = repository_ctx.execute([python3, "-c", "import sysconfig; print(sysconfig.get_path('include'))"])
    if result.return_code != 0:
        fail("Failed to get Python include path")
    python_include = result.stdout.strip()
    
    # Symlink the Python headers directory
    repository_ctx.symlink(python_include, "python_include")
    
    repository_ctx.file("BUILD", """
licenses(["restricted"])

package(default_visibility = ["//visibility:public"])

load("@rules_python//python:py_runtime.bzl", "py_runtime")
load("@rules_python//python:py_runtime_pair.bzl", "py_runtime_pair")

py_runtime(
    name = "py3_runtime",
    interpreter_path = "{python3}",
    python_version = "PY3",
)

py_runtime_pair(
    name = "py_runtime_pair",
    py3_runtime = ":py3_runtime",
)

toolchain(
    name = "py_toolchain",
    toolchain = ":py_runtime_pair",
    toolchain_type = "@rules_python//python:toolchain_type",
)

cc_library(
    name = "python_headers",
    hdrs = glob(["python_include/**/*.h"]),
    includes = ["python_include"],
)
""".format(python3 = python3))
    
local_config_python = repository_rule(
    implementation = _local_config_python_impl,
    local = True,
)
